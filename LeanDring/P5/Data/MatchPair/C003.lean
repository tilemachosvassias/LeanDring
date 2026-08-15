/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C011
import LeanDring.P5.Data.MatchLeaf.C012
import LeanDring.P5.Data.MatchLeaf.C013
import LeanDring.P5.Data.MatchLeaf.C008
import LeanDring.P5.Data.MatchLeaf.C009
import LeanDring.P5.Data.MatchLeaf.C010

/-! # Stage-5 per-pair theorems, chunk 2 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_66_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_35_20 hp j hj hq
  simp at hm

theorem pair_66_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_40_20 hp j hj hq
  simp at hm

theorem pair_66_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_45_20 hp j hj hq
  simp at hm

theorem pair_66_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_50_20 hp j hj hq
  simp at hm

theorem pair_66_66 (p : Nat) (hp : p < (Q2.transData.getD 66 []).length)
    (hrep : (Q2.cosetIsRep.getD 66 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ p hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ p (transLenTr ⟨66, by decide⟩ p hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_66 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_66_66_24 hp j hj hq
  simp at hm

theorem pair_67_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_7_4 hp j hj hq
  simp at hm

theorem pair_67_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_12_4 hp j hj hq
  simp at hm

theorem pair_67_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_25_20 hp j hj hq
  simp at hm

theorem pair_67_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_30_20 hp j hj hq
  simp at hm

theorem pair_67_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_35_20 hp j hj hq
  simp at hm

theorem pair_67_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_40_20 hp j hj hq
  simp at hm

theorem pair_67_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_45_20 hp j hj hq
  simp at hm

theorem pair_67_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_50_20 hp j hj hq
  simp at hm

theorem pair_67_67 (p : Nat) (hp : p < (Q2.transData.getD 67 []).length)
    (hrep : (Q2.cosetIsRep.getD 67 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ p hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ p (transLenTr ⟨67, by decide⟩ p hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_67 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_67_67_120 hp j hj hq
  simp at hm

theorem pair_68_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_6_4 hp j hj hq
  simp at hm

theorem pair_68_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_12_4 hp j hj hq
  simp at hm

theorem pair_68_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_24_20 hp j hj hq
  simp at hm

theorem pair_68_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_30_20 hp j hj hq
  simp at hm

theorem pair_68_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_35_20 hp j hj hq
  simp at hm

theorem pair_68_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_40_20 hp j hj hq
  simp at hm

theorem pair_68_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_45_20 hp j hj hq
  simp at hm

theorem pair_68_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_50_20 hp j hj hq
  simp at hm

theorem pair_68_68 (p : Nat) (hp : p < (Q2.transData.getD 68 []).length)
    (hrep : (Q2.cosetIsRep.getD 68 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ p hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ p (transLenTr ⟨68, by decide⟩ p hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_68 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_68_68_24 hp j hj hq
  simp at hm

theorem pair_69_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_8_4 hp j hj hq
  simp at hm

theorem pair_69_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_12_4 hp j hj hq
  simp at hm

theorem pair_69_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_26_20 hp j hj hq
  simp at hm

theorem pair_69_30 (p : Nat) (hp : p < (Q2.transData.getD 30 []).length)
    (hrep : (Q2.cosetIsRep.getD 30 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ p hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ p (transLenTr ⟨30, by decide⟩ p hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_30 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_30_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_30_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_30_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_30_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_30_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_30_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_30_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_30_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_30_20 hp j hj hq
  simp at hm

theorem pair_69_35 (p : Nat) (hp : p < (Q2.transData.getD 35 []).length)
    (hrep : (Q2.cosetIsRep.getD 35 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ p hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ p (transLenTr ⟨35, by decide⟩ p hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_35 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_35_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_35_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_35_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_35_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_35_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_35_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_35_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_35_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_35_20 hp j hj hq
  simp at hm

theorem pair_69_40 (p : Nat) (hp : p < (Q2.transData.getD 40 []).length)
    (hrep : (Q2.cosetIsRep.getD 40 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ p hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ p (transLenTr ⟨40, by decide⟩ p hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_40 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_40_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_40_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_40_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_40_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_40_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_40_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_40_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_40_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_40_20 hp j hj hq
  simp at hm

theorem pair_69_45 (p : Nat) (hp : p < (Q2.transData.getD 45 []).length)
    (hrep : (Q2.cosetIsRep.getD 45 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ p hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ p (transLenTr ⟨45, by decide⟩ p hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_45 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_45_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_45_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_45_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_45_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_45_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_45_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_45_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_45_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_45_20 hp j hj hq
  simp at hm

theorem pair_69_50 (p : Nat) (hp : p < (Q2.transData.getD 50 []).length)
    (hrep : (Q2.cosetIsRep.getD 50 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ p hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ p (transLenTr ⟨50, by decide⟩ p hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_50 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_50_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_50_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_50_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_50_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_50_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_50_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_50_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_50_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_50_20 hp j hj hq
  simp at hm

theorem pair_69_69 (p : Nat) (hp : p < (Q2.transData.getD 69 []).length)
    (hrep : (Q2.cosetIsRep.getD 69 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨69, by decide⟩ : Fin 148)) (colE2 ⟨69, by decide⟩ p hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨69, by decide⟩ : Fin 148))
        (colE1 ⟨69, by decide⟩ p (transLenTr ⟨69, by decide⟩ p hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_69 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_69_69_24 hp j hj hq
  simp at hm

theorem pair_70_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_9_4 hp j hj hq
  simp at hm

theorem pair_70_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_12_4 hp j hj hq
  simp at hm

theorem pair_70_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_27_20 hp j hj hq
  simp at hm

theorem pair_70_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_31_20 hp j hj hq
  simp at hm

theorem pair_70_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_36_20 hp j hj hq
  simp at hm

theorem pair_70_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_41_20 hp j hj hq
  simp at hm

theorem pair_70_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_46_20 hp j hj hq
  simp at hm

theorem pair_70_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_51_20 hp j hj hq
  simp at hm

theorem pair_70_70 (p : Nat) (hp : p < (Q2.transData.getD 70 []).length)
    (hrep : (Q2.cosetIsRep.getD 70 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 70 []).length)
    (hq : (normIsRep.getD 70 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ p hp)
        (rowE2 (⟨70, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ p (transLenTr ⟨70, by decide⟩ p hp))
        (rowE1 (⟨70, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_70 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_70_70_24 hp j hj hq
  simp at hm

theorem pair_71_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_1_4 hp j hj hq
  simp at hm

theorem pair_71_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_12_4 hp j hj hq
  simp at hm

theorem pair_71_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_19_20 hp j hj hq
  simp at hm

theorem pair_71_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_31_20 hp j hj hq
  simp at hm

theorem pair_71_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_36_20 hp j hj hq
  simp at hm

theorem pair_71_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_41_20 hp j hj hq
  simp at hm

theorem pair_71_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_46_20 hp j hj hq
  simp at hm

theorem pair_71_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_51_20 hp j hj hq
  simp at hm

theorem pair_71_71 (p : Nat) (hp : p < (Q2.transData.getD 71 []).length)
    (hrep : (Q2.cosetIsRep.getD 71 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ p hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ p (transLenTr ⟨71, by decide⟩ p hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_71 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_71_71_24 hp j hj hq
  simp at hm

theorem pair_72_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_7_4 hp j hj hq
  simp at hm

theorem pair_72_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_12_4 hp j hj hq
  simp at hm

theorem pair_72_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_25_20 hp j hj hq
  simp at hm

theorem pair_72_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_31_20 hp j hj hq
  simp at hm

theorem pair_72_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_36_20 hp j hj hq
  simp at hm

theorem pair_72_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_41_20 hp j hj hq
  simp at hm

theorem pair_72_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_46_20 hp j hj hq
  simp at hm

theorem pair_72_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_51_20 hp j hj hq
  simp at hm

theorem pair_72_72 (p : Nat) (hp : p < (Q2.transData.getD 72 []).length)
    (hrep : (Q2.cosetIsRep.getD 72 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ p hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ p (transLenTr ⟨72, by decide⟩ p hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_72 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_72_72_24 hp j hj hq
  simp at hm

theorem pair_73_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_6_4 hp j hj hq
  simp at hm

theorem pair_73_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_12_4 hp j hj hq
  simp at hm

theorem pair_73_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_24_20 hp j hj hq
  simp at hm

theorem pair_73_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_31_20 hp j hj hq
  simp at hm

theorem pair_73_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_36_20 hp j hj hq
  simp at hm

theorem pair_73_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_41_20 hp j hj hq
  simp at hm

theorem pair_73_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_46_20 hp j hj hq
  simp at hm

theorem pair_73_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_51_20 hp j hj hq
  simp at hm

theorem pair_73_73 (p : Nat) (hp : p < (Q2.transData.getD 73 []).length)
    (hrep : (Q2.cosetIsRep.getD 73 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ p hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ p (transLenTr ⟨73, by decide⟩ p hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_73 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_73_73_120 hp j hj hq
  simp at hm

theorem pair_74_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_8_4 hp j hj hq
  simp at hm

theorem pair_74_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_12_4 hp j hj hq
  simp at hm

theorem pair_74_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_26_20 hp j hj hq
  simp at hm

theorem pair_74_31 (p : Nat) (hp : p < (Q2.transData.getD 31 []).length)
    (hrep : (Q2.cosetIsRep.getD 31 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ p hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ p (transLenTr ⟨31, by decide⟩ p hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_31 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_31_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_31_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_31_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_31_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_31_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_31_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_31_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_31_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_31_20 hp j hj hq
  simp at hm

theorem pair_74_36 (p : Nat) (hp : p < (Q2.transData.getD 36 []).length)
    (hrep : (Q2.cosetIsRep.getD 36 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ p hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ p (transLenTr ⟨36, by decide⟩ p hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_36 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_36_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_36_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_36_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_36_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_36_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_36_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_36_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_36_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_36_20 hp j hj hq
  simp at hm

theorem pair_74_41 (p : Nat) (hp : p < (Q2.transData.getD 41 []).length)
    (hrep : (Q2.cosetIsRep.getD 41 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ p hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ p (transLenTr ⟨41, by decide⟩ p hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_41 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_41_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_41_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_41_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_41_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_41_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_41_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_41_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_41_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_41_20 hp j hj hq
  simp at hm

theorem pair_74_46 (p : Nat) (hp : p < (Q2.transData.getD 46 []).length)
    (hrep : (Q2.cosetIsRep.getD 46 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ p hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ p (transLenTr ⟨46, by decide⟩ p hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_46 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_46_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_46_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_46_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_46_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_46_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_46_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_46_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_46_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_46_20 hp j hj hq
  simp at hm

theorem pair_74_51 (p : Nat) (hp : p < (Q2.transData.getD 51 []).length)
    (hrep : (Q2.cosetIsRep.getD 51 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ p hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ p (transLenTr ⟨51, by decide⟩ p hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_51 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_51_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_51_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_51_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_51_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_51_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_51_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_51_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_51_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_51_20 hp j hj hq
  simp at hm

theorem pair_74_74 (p : Nat) (hp : p < (Q2.transData.getD 74 []).length)
    (hrep : (Q2.cosetIsRep.getD 74 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨74, by decide⟩ : Fin 148)) (colE2 ⟨74, by decide⟩ p hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨74, by decide⟩ : Fin 148))
        (colE1 ⟨74, by decide⟩ p (transLenTr ⟨74, by decide⟩ p hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_74 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_74_74_24 hp j hj hq
  simp at hm

theorem pair_75_9 (p : Nat) (hp : p < (Q2.transData.getD 9 []).length)
    (hrep : (Q2.cosetIsRep.getD 9 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ p hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ p (transLenTr ⟨9, by decide⟩ p hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_9 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_9_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_9_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_9_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_9_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_9_4 hp j hj hq
  simp at hm

theorem pair_75_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_12_4 hp j hj hq
  simp at hm

theorem pair_75_27 (p : Nat) (hp : p < (Q2.transData.getD 27 []).length)
    (hrep : (Q2.cosetIsRep.getD 27 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ p hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ p (transLenTr ⟨27, by decide⟩ p hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_27 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_27_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_27_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_27_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_27_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_27_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_27_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_27_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_27_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_27_20 hp j hj hq
  simp at hm

theorem pair_75_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_32_20 hp j hj hq
  simp at hm

theorem pair_75_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_37_20 hp j hj hq
  simp at hm

theorem pair_75_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_42_20 hp j hj hq
  simp at hm

theorem pair_75_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_47_20 hp j hj hq
  simp at hm

theorem pair_75_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_52_20 hp j hj hq
  simp at hm

theorem pair_75_75 (p : Nat) (hp : p < (Q2.transData.getD 75 []).length)
    (hrep : (Q2.cosetIsRep.getD 75 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 75 []).length)
    (hq : (normIsRep.getD 75 []).getD j false = true) :
    species (Q2.reps (⟨75, by decide⟩ : Fin 148)) (colE2 ⟨75, by decide⟩ p hp)
        (rowE2 (⟨75, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨75, by decide⟩ : Fin 148))
        (colE1 ⟨75, by decide⟩ p (transLenTr ⟨75, by decide⟩ p hp))
        (rowE1 (⟨75, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_75 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_75_75_24 hp j hj hq
  simp at hm

theorem pair_76_1 (p : Nat) (hp : p < (Q2.transData.getD 1 []).length)
    (hrep : (Q2.cosetIsRep.getD 1 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ p hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ p (transLenTr ⟨1, by decide⟩ p hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_1 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_1_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_1_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_1_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_1_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_1_4 hp j hj hq
  simp at hm

theorem pair_76_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_12_4 hp j hj hq
  simp at hm

theorem pair_76_19 (p : Nat) (hp : p < (Q2.transData.getD 19 []).length)
    (hrep : (Q2.cosetIsRep.getD 19 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ p hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ p (transLenTr ⟨19, by decide⟩ p hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_19 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_19_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_19_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_19_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_19_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_19_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_19_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_19_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_19_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_19_20 hp j hj hq
  simp at hm

theorem pair_76_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_32_20 hp j hj hq
  simp at hm

theorem pair_76_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_37_20 hp j hj hq
  simp at hm

theorem pair_76_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_42_20 hp j hj hq
  simp at hm

theorem pair_76_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_47_20 hp j hj hq
  simp at hm

theorem pair_76_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_52_20 hp j hj hq
  simp at hm

theorem pair_76_76 (p : Nat) (hp : p < (Q2.transData.getD 76 []).length)
    (hrep : (Q2.cosetIsRep.getD 76 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 76 []).length)
    (hq : (normIsRep.getD 76 []).getD j false = true) :
    species (Q2.reps (⟨76, by decide⟩ : Fin 148)) (colE2 ⟨76, by decide⟩ p hp)
        (rowE2 (⟨76, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨76, by decide⟩ : Fin 148))
        (colE1 ⟨76, by decide⟩ p (transLenTr ⟨76, by decide⟩ p hp))
        (rowE1 (⟨76, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_76 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_76_76_120 hp j hj hq
  simp at hm

theorem pair_77_7 (p : Nat) (hp : p < (Q2.transData.getD 7 []).length)
    (hrep : (Q2.cosetIsRep.getD 7 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ p hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ p (transLenTr ⟨7, by decide⟩ p hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_7 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_7_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_7_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_7_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_7_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_7_4 hp j hj hq
  simp at hm

theorem pair_77_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_12_4 hp j hj hq
  simp at hm

theorem pair_77_25 (p : Nat) (hp : p < (Q2.transData.getD 25 []).length)
    (hrep : (Q2.cosetIsRep.getD 25 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ p hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ p (transLenTr ⟨25, by decide⟩ p hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_25 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_25_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_25_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_25_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_25_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_25_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_25_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_25_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_25_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_25_20 hp j hj hq
  simp at hm

theorem pair_77_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_32_20 hp j hj hq
  simp at hm

theorem pair_77_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_37_20 hp j hj hq
  simp at hm

theorem pair_77_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_42_20 hp j hj hq
  simp at hm

theorem pair_77_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_47_20 hp j hj hq
  simp at hm

theorem pair_77_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_52_20 hp j hj hq
  simp at hm

theorem pair_77_77 (p : Nat) (hp : p < (Q2.transData.getD 77 []).length)
    (hrep : (Q2.cosetIsRep.getD 77 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 77 []).length)
    (hq : (normIsRep.getD 77 []).getD j false = true) :
    species (Q2.reps (⟨77, by decide⟩ : Fin 148)) (colE2 ⟨77, by decide⟩ p hp)
        (rowE2 (⟨77, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨77, by decide⟩ : Fin 148))
        (colE1 ⟨77, by decide⟩ p (transLenTr ⟨77, by decide⟩ p hp))
        (rowE1 (⟨77, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_77 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_77_77_24 hp j hj hq
  simp at hm

theorem pair_78_6 (p : Nat) (hp : p < (Q2.transData.getD 6 []).length)
    (hrep : (Q2.cosetIsRep.getD 6 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ p hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ p (transLenTr ⟨6, by decide⟩ p hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_6 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_6_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_6_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_6_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_6_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_6_4 hp j hj hq
  simp at hm

theorem pair_78_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_12_4 hp j hj hq
  simp at hm

theorem pair_78_24 (p : Nat) (hp : p < (Q2.transData.getD 24 []).length)
    (hrep : (Q2.cosetIsRep.getD 24 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ p hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ p (transLenTr ⟨24, by decide⟩ p hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_24 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_24_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_24_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_24_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_24_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_24_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_24_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_24_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_24_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_24_20 hp j hj hq
  simp at hm

theorem pair_78_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_32_20 hp j hj hq
  simp at hm

theorem pair_78_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_37_20 hp j hj hq
  simp at hm

theorem pair_78_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_42_20 hp j hj hq
  simp at hm

theorem pair_78_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_47_20 hp j hj hq
  simp at hm

theorem pair_78_52 (p : Nat) (hp : p < (Q2.transData.getD 52 []).length)
    (hrep : (Q2.cosetIsRep.getD 52 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ p hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ p (transLenTr ⟨52, by decide⟩ p hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_52 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_52_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_52_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_52_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_52_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_52_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_52_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_52_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_52_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_52_20 hp j hj hq
  simp at hm

theorem pair_78_78 (p : Nat) (hp : p < (Q2.transData.getD 78 []).length)
    (hrep : (Q2.cosetIsRep.getD 78 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 78 []).length)
    (hq : (normIsRep.getD 78 []).getD j false = true) :
    species (Q2.reps (⟨78, by decide⟩ : Fin 148)) (colE2 ⟨78, by decide⟩ p hp)
        (rowE2 (⟨78, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨78, by decide⟩ : Fin 148))
        (colE1 ⟨78, by decide⟩ p (transLenTr ⟨78, by decide⟩ p hp))
        (rowE1 (⟨78, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_78 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_78_78_24 hp j hj hq
  simp at hm

theorem pair_79_8 (p : Nat) (hp : p < (Q2.transData.getD 8 []).length)
    (hrep : (Q2.cosetIsRep.getD 8 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ p hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ p (transLenTr ⟨8, by decide⟩ p hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_8 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_8_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_8_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_8_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_8_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_8_4 hp j hj hq
  simp at hm

theorem pair_79_12 (p : Nat) (hp : p < (Q2.transData.getD 12 []).length)
    (hrep : (Q2.cosetIsRep.getD 12 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ p hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ p (transLenTr ⟨12, by decide⟩ p hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_12 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_12_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_12_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_12_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_12_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_12_4 hp j hj hq
  simp at hm

theorem pair_79_26 (p : Nat) (hp : p < (Q2.transData.getD 26 []).length)
    (hrep : (Q2.cosetIsRep.getD 26 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ p hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ p (transLenTr ⟨26, by decide⟩ p hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_26 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_26_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_26_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_26_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_26_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_26_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_26_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_26_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_26_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_26_20 hp j hj hq
  simp at hm

theorem pair_79_32 (p : Nat) (hp : p < (Q2.transData.getD 32 []).length)
    (hrep : (Q2.cosetIsRep.getD 32 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨32, by decide⟩ : Fin 148)) (colE2 ⟨32, by decide⟩ p hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨32, by decide⟩ : Fin 148))
        (colE1 ⟨32, by decide⟩ p (transLenTr ⟨32, by decide⟩ p hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_32 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_32_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_32_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_32_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_32_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_32_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_32_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_32_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_32_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_32_20 hp j hj hq
  simp at hm

theorem pair_79_37 (p : Nat) (hp : p < (Q2.transData.getD 37 []).length)
    (hrep : (Q2.cosetIsRep.getD 37 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ p hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ p (transLenTr ⟨37, by decide⟩ p hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_37 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_37_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_37_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_37_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_37_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_37_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_37_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_37_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_37_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_37_20 hp j hj hq
  simp at hm

theorem pair_79_42 (p : Nat) (hp : p < (Q2.transData.getD 42 []).length)
    (hrep : (Q2.cosetIsRep.getD 42 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨42, by decide⟩ : Fin 148)) (colE2 ⟨42, by decide⟩ p hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨42, by decide⟩ : Fin 148))
        (colE1 ⟨42, by decide⟩ p (transLenTr ⟨42, by decide⟩ p hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_42 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_42_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_42_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_42_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_42_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_42_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_42_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_42_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_42_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_42_20 hp j hj hq
  simp at hm

theorem pair_79_47 (p : Nat) (hp : p < (Q2.transData.getD 47 []).length)
    (hrep : (Q2.cosetIsRep.getD 47 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 79 []).length)
    (hq : (normIsRep.getD 79 []).getD j false = true) :
    species (Q2.reps (⟨47, by decide⟩ : Fin 148)) (colE2 ⟨47, by decide⟩ p hp)
        (rowE2 (⟨79, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨47, by decide⟩ : Fin 148))
        (colE1 ⟨47, by decide⟩ p (transLenTr ⟨47, by decide⟩ p hp))
        (rowE1 (⟨79, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_47 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_47_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_47_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_47_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_47_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_47_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_47_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_47_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_47_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_79_47_20 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
