/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C042
import LeanDring.P5.Data.MatchLeaf.C043
import LeanDring.P5.Data.MatchLeaf.C044
import LeanDring.P5.Data.MatchLeaf.C045
import LeanDring.P5.Data.MatchLeaf.C046
import LeanDring.P5.Data.MatchLeaf.C047

/-! # Stage-5 per-pair theorems, chunk 9 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_139_96 (p : Nat) (hp : p < (Q2.transData.getD 96 []).length)
    (hrep : (Q2.cosetIsRep.getD 96 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ p (transLenTr ⟨96, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_96 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_96_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_96_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_96_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_96_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_96_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_96_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_96_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_96_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_96_20 hp j hj hq
  simp at hm

theorem pair_139_100 (p : Nat) (hp : p < (Q2.transData.getD 100 []).length)
    (hrep : (Q2.cosetIsRep.getD 100 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ p (transLenTr ⟨100, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_100 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_100_100 hp j hj hq
  simp at hm

theorem pair_139_107 (p : Nat) (hp : p < (Q2.transData.getD 107 []).length)
    (hrep : (Q2.cosetIsRep.getD 107 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ p (transLenTr ⟨107, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_107 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_107_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_107_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_107_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_107_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_107_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_107_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_107_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_107_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_107_20 hp j hj hq
  simp at hm

theorem pair_139_113 (p : Nat) (hp : p < (Q2.transData.getD 113 []).length)
    (hrep : (Q2.cosetIsRep.getD 113 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ p (transLenTr ⟨113, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_113 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_113_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_113_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_113_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_113_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_113_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_113_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_113_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_113_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_113_20 hp j hj hq
  simp at hm

theorem pair_139_139 (p : Nat) (hp : p < (Q2.transData.getD 139 []).length)
    (hrep : (Q2.cosetIsRep.getD 139 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 139 []).length)
    (hq : (normIsRep.getD 139 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ p hp)
        (rowE2 (⟨139, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ p (transLenTr ⟨139, by decide⟩ p hp))
        (rowE1 (⟨139, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_139 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_139_139_24 hp j hj hq
  simp at hm

theorem pair_140_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_5_4 hp j hj hq
  simp at hm

theorem pair_140_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_10_4 hp j hj hq
  simp at hm

theorem pair_140_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_12_4 hp j hj hq
  simp at hm

theorem pair_140_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_23_20 hp j hj hq
  simp at hm

theorem pair_140_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_28_20 hp j hj hq
  simp at hm

theorem pair_140_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_35_20 hp j hj hq
  simp at hm

theorem pair_140_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_39_20 hp j hj hq
  simp at hm

theorem pair_140_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_46_20 hp j hj hq
  simp at hm

theorem pair_140_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_52_20 hp j hj hq
  simp at hm

theorem pair_140_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_53_20 hp j hj hq
  simp at hm

theorem pair_140_84 (p : Nat) (hp : p < (Q2.transData.getD 84 []).length)
    (hrep : (Q2.cosetIsRep.getD 84 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ p (transLenTr ⟨84, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_84 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_84_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_84_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_84_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_84_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_84_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_84_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_84_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_84_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_84_20 hp j hj hq
  simp at hm

theorem pair_140_90 (p : Nat) (hp : p < (Q2.transData.getD 90 []).length)
    (hrep : (Q2.cosetIsRep.getD 90 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ p (transLenTr ⟨90, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_90 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_90_100 hp j hj hq
  simp at hm

theorem pair_140_97 (p : Nat) (hp : p < (Q2.transData.getD 97 []).length)
    (hrep : (Q2.cosetIsRep.getD 97 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ p (transLenTr ⟨97, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_97 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_97_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_97_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_97_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_97_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_97_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_97_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_97_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_97_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_97_20 hp j hj hq
  simp at hm

theorem pair_140_101 (p : Nat) (hp : p < (Q2.transData.getD 101 []).length)
    (hrep : (Q2.cosetIsRep.getD 101 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ p (transLenTr ⟨101, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_101 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_101_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_101_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_101_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_101_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_101_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_101_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_101_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_101_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_101_20 hp j hj hq
  simp at hm

theorem pair_140_108 (p : Nat) (hp : p < (Q2.transData.getD 108 []).length)
    (hrep : (Q2.cosetIsRep.getD 108 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ p (transLenTr ⟨108, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_108 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_108_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_108_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_108_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_108_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_108_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_108_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_108_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_108_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_108_20 hp j hj hq
  simp at hm

theorem pair_140_114 (p : Nat) (hp : p < (Q2.transData.getD 114 []).length)
    (hrep : (Q2.cosetIsRep.getD 114 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ p (transLenTr ⟨114, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_114 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_114_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_114_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_114_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_114_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_114_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_114_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_114_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_114_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_114_20 hp j hj hq
  simp at hm

theorem pair_140_140 (p : Nat) (hp : p < (Q2.transData.getD 140 []).length)
    (hrep : (Q2.cosetIsRep.getD 140 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 140 []).length)
    (hq : (normIsRep.getD 140 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ p hp)
        (rowE2 (⟨140, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ p (transLenTr ⟨140, by decide⟩ p hp))
        (rowE1 (⟨140, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_140 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_140_140_24 hp j hj hq
  simp at hm

theorem pair_141_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_1_4 hp j hj hq
  simp at hm

theorem pair_141_2 (p : Nat) (hp : p < (Q2.transData.getD 2 []).length)
    (hrep : (Q2.cosetIsRep.getD 2 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ p (transLenTr ⟨2, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_2 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_2_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_2_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_2_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_2_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_2_4 hp j hj hq
  simp at hm

theorem pair_141_3 (p : Nat) (hp : p < (Q2.transData.getD 3 []).length)
    (hrep : (Q2.cosetIsRep.getD 3 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ p (transLenTr ⟨3, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_3 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_3_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_3_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_3_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_3_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_3_4 hp j hj hq
  simp at hm

theorem pair_141_4 (p : Nat) (hp : p < (Q2.transData.getD 4 []).length)
    (hrep : (Q2.cosetIsRep.getD 4 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ p (transLenTr ⟨4, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_4 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_4_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_4_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_4_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_4_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_4_4 hp j hj hq
  simp at hm

theorem pair_141_5 (p : Nat) (hp : p < (Q2.transData.getD 5 []).length)
    (hrep : (Q2.cosetIsRep.getD 5 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ p (transLenTr ⟨5, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_5 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_5_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_5_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_5_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_5_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_5_4 hp j hj hq
  simp at hm

theorem pair_141_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_6_4 hp j hj hq
  simp at hm

theorem pair_141_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_7_4 hp j hj hq
  simp at hm

theorem pair_141_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_8_4 hp j hj hq
  simp at hm

theorem pair_141_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_9_4 hp j hj hq
  simp at hm

theorem pair_141_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_10_4 hp j hj hq
  simp at hm

theorem pair_141_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_11_4 hp j hj hq
  simp at hm

theorem pair_141_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_12_4 hp j hj hq
  simp at hm

theorem pair_141_13 (p : Nat) (hp : p < (Q2.transData.getD 13 []).length)
    (hrep : (Q2.cosetIsRep.getD 13 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ p (transLenTr ⟨13, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_13 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_13_24 hp j hj hq
  simp at hm

theorem pair_141_14 (p : Nat) (hp : p < (Q2.transData.getD 14 []).length)
    (hrep : (Q2.cosetIsRep.getD 14 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ p (transLenTr ⟨14, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_14 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_14_24 hp j hj hq
  simp at hm

theorem pair_141_15 (p : Nat) (hp : p < (Q2.transData.getD 15 []).length)
    (hrep : (Q2.cosetIsRep.getD 15 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ p (transLenTr ⟨15, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_15 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_15_24 hp j hj hq
  simp at hm

theorem pair_141_16 (p : Nat) (hp : p < (Q2.transData.getD 16 []).length)
    (hrep : (Q2.cosetIsRep.getD 16 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ p (transLenTr ⟨16, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_16 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_16_24 hp j hj hq
  simp at hm

theorem pair_141_17 (p : Nat) (hp : p < (Q2.transData.getD 17 []).length)
    (hrep : (Q2.cosetIsRep.getD 17 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ p (transLenTr ⟨17, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_17 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_17_24 hp j hj hq
  simp at hm

theorem pair_141_18 (p : Nat) (hp : p < (Q2.transData.getD 18 []).length)
    (hrep : (Q2.cosetIsRep.getD 18 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ p (transLenTr ⟨18, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_18 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_18_24 hp j hj hq
  simp at hm

theorem pair_141_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_19_20 hp j hj hq
  simp at hm

theorem pair_141_20 (p : Nat) (hp : p < (Q2.transData.getD 20 []).length)
    (hrep : (Q2.cosetIsRep.getD 20 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ p (transLenTr ⟨20, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_20 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_20_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_20_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_20_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_20_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_20_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_20_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_20_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_20_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_20_20 hp j hj hq
  simp at hm

theorem pair_141_21 (p : Nat) (hp : p < (Q2.transData.getD 21 []).length)
    (hrep : (Q2.cosetIsRep.getD 21 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ p (transLenTr ⟨21, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_21 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_21_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_21_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_21_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_21_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_21_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_21_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_21_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_21_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_21_20 hp j hj hq
  simp at hm

theorem pair_141_22 (p : Nat) (hp : p < (Q2.transData.getD 22 []).length)
    (hrep : (Q2.cosetIsRep.getD 22 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ p (transLenTr ⟨22, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_22 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_22_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_22_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_22_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_22_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_22_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_22_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_22_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_22_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_22_20 hp j hj hq
  simp at hm

theorem pair_141_23 (p : Nat) (hp : p < (Q2.transData.getD 23 []).length)
    (hrep : (Q2.cosetIsRep.getD 23 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ p (transLenTr ⟨23, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_23 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_23_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_23_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_23_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_23_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_23_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_23_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_23_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_23_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_23_20 hp j hj hq
  simp at hm

theorem pair_141_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_24_20 hp j hj hq
  simp at hm

theorem pair_141_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_25_20 hp j hj hq
  simp at hm

theorem pair_141_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_26_20 hp j hj hq
  simp at hm

theorem pair_141_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_27_20 hp j hj hq
  simp at hm

theorem pair_141_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_53_20 hp j hj hq
  simp at hm

theorem pair_141_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_54_20 hp j hj hq
  simp at hm

theorem pair_141_80 (p : Nat) (hp : p < (Q2.transData.getD 80 []).length)
    (hrep : (Q2.cosetIsRep.getD 80 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ p (transLenTr ⟨80, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_80 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_80_120 hp j hj hq
  simp at hm

theorem pair_141_81 (p : Nat) (hp : p < (Q2.transData.getD 81 []).length)
    (hrep : (Q2.cosetIsRep.getD 81 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ p (transLenTr ⟨81, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_81 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_81_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_81_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_81_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_81_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_81_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_81_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_81_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_81_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_81_20 hp j hj hq
  simp at hm

theorem pair_141_82 (p : Nat) (hp : p < (Q2.transData.getD 82 []).length)
    (hrep : (Q2.cosetIsRep.getD 82 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ p (transLenTr ⟨82, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_82 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_82_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_82_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_82_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_82_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_82_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_82_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_82_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_82_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_82_20 hp j hj hq
  simp at hm

theorem pair_141_83 (p : Nat) (hp : p < (Q2.transData.getD 83 []).length)
    (hrep : (Q2.cosetIsRep.getD 83 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ p (transLenTr ⟨83, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_83 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_83_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_83_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_83_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_83_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_83_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_83_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_83_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_83_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_83_20 hp j hj hq
  simp at hm

theorem pair_141_84 (p : Nat) (hp : p < (Q2.transData.getD 84 []).length)
    (hrep : (Q2.cosetIsRep.getD 84 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ p (transLenTr ⟨84, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_84 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_84_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_84_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_84_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_84_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_84_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_84_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_84_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_84_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_84_20 hp j hj hq
  simp at hm

theorem pair_141_85 (p : Nat) (hp : p < (Q2.transData.getD 85 []).length)
    (hrep : (Q2.cosetIsRep.getD 85 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ p (transLenTr ⟨85, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_85 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_85_120 hp j hj hq
  simp at hm

theorem pair_141_86 (p : Nat) (hp : p < (Q2.transData.getD 86 []).length)
    (hrep : (Q2.cosetIsRep.getD 86 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ p (transLenTr ⟨86, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_86 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_86_24 hp j hj hq
  simp at hm

theorem pair_141_87 (p : Nat) (hp : p < (Q2.transData.getD 87 []).length)
    (hrep : (Q2.cosetIsRep.getD 87 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ p (transLenTr ⟨87, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_87 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_87_24 hp j hj hq
  simp at hm

theorem pair_141_88 (p : Nat) (hp : p < (Q2.transData.getD 88 []).length)
    (hrep : (Q2.cosetIsRep.getD 88 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ p (transLenTr ⟨88, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_88 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_88_24 hp j hj hq
  simp at hm

theorem pair_141_89 (p : Nat) (hp : p < (Q2.transData.getD 89 []).length)
    (hrep : (Q2.cosetIsRep.getD 89 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨89, by decide⟩ : Fin 148)) (colE2 ⟨89, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨89, by decide⟩ : Fin 148))
        (colE1 ⟨89, by decide⟩ p (transLenTr ⟨89, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_89 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_89_24 hp j hj hq
  simp at hm

theorem pair_141_115 (p : Nat) (hp : p < (Q2.transData.getD 115 []).length)
    (hrep : (Q2.cosetIsRep.getD 115 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ p (transLenTr ⟨115, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_115 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_115_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_115_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_115_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_115_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_115_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_115_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_115_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_115_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_115_20 hp j hj hq
  simp at hm

theorem pair_141_141 (p : Nat) (hp : p < (Q2.transData.getD 141 []).length)
    (hrep : (Q2.cosetIsRep.getD 141 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ p hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ p (transLenTr ⟨141, by decide⟩ p hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_141 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_141_141_120 hp j hj hq
  simp at hm

theorem pair_142_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_10_4 hp j hj hq
  simp at hm

theorem pair_142_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_11_4 hp j hj hq
  simp at hm

theorem pair_142_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_12_4 hp j hj hq
  simp at hm

theorem pair_142_28 (p : Nat) (hp : p < (Q2.transData.getD 28 []).length)
    (hrep : (Q2.cosetIsRep.getD 28 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ p (transLenTr ⟨28, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_28 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_28_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_28_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_28_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_28_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_28_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_28_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_28_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_28_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_28_20 hp j hj hq
  simp at hm

theorem pair_142_29 (p : Nat) (hp : p < (Q2.transData.getD 29 []).length)
    (hrep : (Q2.cosetIsRep.getD 29 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ p (transLenTr ⟨29, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_29 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_29_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_29_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_29_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_29_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_29_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_29_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_29_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_29_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_29_20 hp j hj hq
  simp at hm

theorem pair_142_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_30_20 hp j hj hq
  simp at hm

theorem pair_142_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_31_20 hp j hj hq
  simp at hm

theorem pair_142_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_32_20 hp j hj hq
  simp at hm

theorem pair_142_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_53_20 hp j hj hq
  simp at hm

theorem pair_142_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_54_20 hp j hj hq
  simp at hm

theorem pair_142_90 (p : Nat) (hp : p < (Q2.transData.getD 90 []).length)
    (hrep : (Q2.cosetIsRep.getD 90 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ p (transLenTr ⟨90, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_90 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_90_100 hp j hj hq
  simp at hm

theorem pair_142_91 (p : Nat) (hp : p < (Q2.transData.getD 91 []).length)
    (hrep : (Q2.cosetIsRep.getD 91 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ p (transLenTr ⟨91, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_91 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_91_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_91_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_91_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_91_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_91_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_91_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_91_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_91_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_91_20 hp j hj hq
  simp at hm

theorem pair_142_92 (p : Nat) (hp : p < (Q2.transData.getD 92 []).length)
    (hrep : (Q2.cosetIsRep.getD 92 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ p (transLenTr ⟨92, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_92 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_92_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_92_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_92_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_92_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_92_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_92_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_92_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_92_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_92_20 hp j hj hq
  simp at hm

theorem pair_142_93 (p : Nat) (hp : p < (Q2.transData.getD 93 []).length)
    (hrep : (Q2.cosetIsRep.getD 93 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ p (transLenTr ⟨93, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_93 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_93_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_93_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_93_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_93_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_93_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_93_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_93_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_93_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_93_20 hp j hj hq
  simp at hm

theorem pair_142_94 (p : Nat) (hp : p < (Q2.transData.getD 94 []).length)
    (hrep : (Q2.cosetIsRep.getD 94 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ p (transLenTr ⟨94, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_94 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_94_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_94_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_94_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_94_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_94_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_94_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_94_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_94_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_94_20 hp j hj hq
  simp at hm

theorem pair_142_115 (p : Nat) (hp : p < (Q2.transData.getD 115 []).length)
    (hrep : (Q2.cosetIsRep.getD 115 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ p (transLenTr ⟨115, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_115 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_115_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_115_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_115_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_115_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_115_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_115_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_115_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_115_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_115_20 hp j hj hq
  simp at hm

theorem pair_142_142 (p : Nat) (hp : p < (Q2.transData.getD 142 []).length)
    (hrep : (Q2.cosetIsRep.getD 142 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 142 []).length)
    (hq : (normIsRep.getD 142 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ p hp)
        (rowE2 (⟨142, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ p (transLenTr ⟨142, by decide⟩ p hp))
        (rowE1 (⟨142, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_142 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_142_142_24 hp j hj hq
  simp at hm

theorem pair_143_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_10_4 hp j hj hq
  simp at hm

theorem pair_143_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_11_4 hp j hj hq
  simp at hm

theorem pair_143_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_12_4 hp j hj hq
  simp at hm

theorem pair_143_33 (p : Nat) (hp : p < (Q2.transData.getD 33 []).length)
    (hrep : (Q2.cosetIsRep.getD 33 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ p (transLenTr ⟨33, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_33 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_33_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_33_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_33_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_33_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_33_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_33_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_33_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_33_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_33_20 hp j hj hq
  simp at hm

theorem pair_143_34 (p : Nat) (hp : p < (Q2.transData.getD 34 []).length)
    (hrep : (Q2.cosetIsRep.getD 34 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ p (transLenTr ⟨34, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_34 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_34_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_34_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_34_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_34_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_34_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_34_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_34_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_34_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_34_20 hp j hj hq
  simp at hm

theorem pair_143_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_35_20 hp j hj hq
  simp at hm

theorem pair_143_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_36_20 hp j hj hq
  simp at hm

theorem pair_143_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_37_20 hp j hj hq
  simp at hm

theorem pair_143_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_53_20 hp j hj hq
  simp at hm

theorem pair_143_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_54_20 hp j hj hq
  simp at hm

theorem pair_143_95 (p : Nat) (hp : p < (Q2.transData.getD 95 []).length)
    (hrep : (Q2.cosetIsRep.getD 95 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ p (transLenTr ⟨95, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_95 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_95_100 hp j hj hq
  simp at hm

theorem pair_143_96 (p : Nat) (hp : p < (Q2.transData.getD 96 []).length)
    (hrep : (Q2.cosetIsRep.getD 96 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ p (transLenTr ⟨96, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_96 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_96_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_96_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_96_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_96_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_96_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_96_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_96_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_96_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_96_20 hp j hj hq
  simp at hm

theorem pair_143_97 (p : Nat) (hp : p < (Q2.transData.getD 97 []).length)
    (hrep : (Q2.cosetIsRep.getD 97 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ p (transLenTr ⟨97, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_97 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_97_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_97_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_97_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_97_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_97_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_97_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_97_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_97_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_97_20 hp j hj hq
  simp at hm

theorem pair_143_98 (p : Nat) (hp : p < (Q2.transData.getD 98 []).length)
    (hrep : (Q2.cosetIsRep.getD 98 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ p (transLenTr ⟨98, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_98 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_98_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_98_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_98_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_98_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_98_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_98_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_98_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_98_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_98_20 hp j hj hq
  simp at hm

theorem pair_143_99 (p : Nat) (hp : p < (Q2.transData.getD 99 []).length)
    (hrep : (Q2.cosetIsRep.getD 99 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ p (transLenTr ⟨99, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_99 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_99_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_99_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_99_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_99_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_99_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_99_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_99_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_99_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_99_20 hp j hj hq
  simp at hm

theorem pair_143_115 (p : Nat) (hp : p < (Q2.transData.getD 115 []).length)
    (hrep : (Q2.cosetIsRep.getD 115 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ p (transLenTr ⟨115, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_115 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_115_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_115_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_115_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_115_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_115_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_115_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_115_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_115_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_115_20 hp j hj hq
  simp at hm

theorem pair_143_143 (p : Nat) (hp : p < (Q2.transData.getD 143 []).length)
    (hrep : (Q2.cosetIsRep.getD 143 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 143 []).length)
    (hq : (normIsRep.getD 143 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ p hp)
        (rowE2 (⟨143, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ p (transLenTr ⟨143, by decide⟩ p hp))
        (rowE1 (⟨143, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_143 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_143_143_24 hp j hj hq
  simp at hm

theorem pair_144_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_10_4 hp j hj hq
  simp at hm

theorem pair_144_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_11_4 hp j hj hq
  simp at hm

theorem pair_144_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_12_4 hp j hj hq
  simp at hm

theorem pair_144_38 (p : Nat) (hp : p < (Q2.transData.getD 38 []).length)
    (hrep : (Q2.cosetIsRep.getD 38 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ p (transLenTr ⟨38, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_38 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_38_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_38_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_38_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_38_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_38_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_38_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_38_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_38_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_38_20 hp j hj hq
  simp at hm

theorem pair_144_39 (p : Nat) (hp : p < (Q2.transData.getD 39 []).length)
    (hrep : (Q2.cosetIsRep.getD 39 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ p (transLenTr ⟨39, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_39 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_39_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_39_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_39_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_39_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_39_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_39_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_39_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_39_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_39_20 hp j hj hq
  simp at hm

theorem pair_144_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_40_20 hp j hj hq
  simp at hm

theorem pair_144_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_41_20 hp j hj hq
  simp at hm

theorem pair_144_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_42_20 hp j hj hq
  simp at hm

theorem pair_144_53 (p : Nat) (hp : p < (Q2.transData.getD 53 []).length)
    (hrep : (Q2.cosetIsRep.getD 53 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ p (transLenTr ⟨53, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_53 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_53_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_53_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_53_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_53_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_53_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_53_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_53_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_53_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_53_20 hp j hj hq
  simp at hm

theorem pair_144_54 (p : Nat) (hp : p < (Q2.transData.getD 54 []).length)
    (hrep : (Q2.cosetIsRep.getD 54 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ p (transLenTr ⟨54, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_54 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_54_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_54_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_54_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_54_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_54_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_54_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_54_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_54_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_54_20 hp j hj hq
  simp at hm

theorem pair_144_100 (p : Nat) (hp : p < (Q2.transData.getD 100 []).length)
    (hrep : (Q2.cosetIsRep.getD 100 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ p (transLenTr ⟨100, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_100 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_100_100 hp j hj hq
  simp at hm

theorem pair_144_101 (p : Nat) (hp : p < (Q2.transData.getD 101 []).length)
    (hrep : (Q2.cosetIsRep.getD 101 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ p (transLenTr ⟨101, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_101 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_101_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_101_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_101_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_101_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_101_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_101_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_101_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_101_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_101_20 hp j hj hq
  simp at hm

theorem pair_144_102 (p : Nat) (hp : p < (Q2.transData.getD 102 []).length)
    (hrep : (Q2.cosetIsRep.getD 102 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ p (transLenTr ⟨102, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_102 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_102_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_102_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_102_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_102_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_102_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_102_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_102_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_102_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_102_20 hp j hj hq
  simp at hm

theorem pair_144_103 (p : Nat) (hp : p < (Q2.transData.getD 103 []).length)
    (hrep : (Q2.cosetIsRep.getD 103 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ p (transLenTr ⟨103, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_103 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_103_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_103_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_103_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_103_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_103_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_103_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_103_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_103_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_103_20 hp j hj hq
  simp at hm

theorem pair_144_104 (p : Nat) (hp : p < (Q2.transData.getD 104 []).length)
    (hrep : (Q2.cosetIsRep.getD 104 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ p (transLenTr ⟨104, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_104 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_104_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_104_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_104_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_104_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_104_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_104_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_104_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_104_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_104_20 hp j hj hq
  simp at hm

theorem pair_144_115 (p : Nat) (hp : p < (Q2.transData.getD 115 []).length)
    (hrep : (Q2.cosetIsRep.getD 115 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ p (transLenTr ⟨115, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_115 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_115_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_115_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_115_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_115_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_115_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_115_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_115_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_115_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_115_20 hp j hj hq
  simp at hm

theorem pair_144_144 (p : Nat) (hp : p < (Q2.transData.getD 144 []).length)
    (hrep : (Q2.cosetIsRep.getD 144 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 144 []).length)
    (hq : (normIsRep.getD 144 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ p hp)
        (rowE2 (⟨144, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ p (transLenTr ⟨144, by decide⟩ p hp))
        (rowE1 (⟨144, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_144 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_144_144_24 hp j hj hq
  simp at hm

theorem pair_145_10 (p : Nat) (hp : p < (Q2.transData.getD 10 []).length)
    (hrep : (Q2.cosetIsRep.getD 10 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ p (transLenTr ⟨10, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_10 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_10_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_10_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_10_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_10_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_10_4 hp j hj hq
  simp at hm

theorem pair_145_11 (p : Nat) (hp : p < (Q2.transData.getD 11 []).length)
    (hrep : (Q2.cosetIsRep.getD 11 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ p (transLenTr ⟨11, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_11 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_11_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_11_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_11_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_11_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_11_4 hp j hj hq
  simp at hm

theorem pair_145_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_12_4 hp j hj hq
  simp at hm

theorem pair_145_43 (p : Nat) (hp : p < (Q2.transData.getD 43 []).length)
    (hrep : (Q2.cosetIsRep.getD 43 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ p (transLenTr ⟨43, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_43 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_43_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_43_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_43_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_43_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_43_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_43_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_43_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_43_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_43_20 hp j hj hq
  simp at hm

theorem pair_145_44 (p : Nat) (hp : p < (Q2.transData.getD 44 []).length)
    (hrep : (Q2.cosetIsRep.getD 44 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ p (transLenTr ⟨44, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_44 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_44_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_44_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_44_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_44_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_44_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_44_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_44_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_44_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_44_20 hp j hj hq
  simp at hm

theorem pair_145_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 145 []).length)
    (hq : (normIsRep.getD 145 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨145, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨145, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_145_45_20 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
