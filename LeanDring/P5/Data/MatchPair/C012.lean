/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.MatchLeaf.C054
import LeanDring.P5.Data.MatchLeaf.C055
import LeanDring.P5.Data.MatchLeaf.C056
import LeanDring.P5.Data.MatchLeaf.C057
import LeanDring.P5.Data.MatchLeaf.C058
import LeanDring.P5.Data.MatchLeaf.C059

/-! # Stage-5 per-pair theorems, chunk 11 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem pair_147_93 (p : Nat) (hp : p < (Q2.transData.getD 93 []).length)
    (hrep : (Q2.cosetIsRep.getD 93 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨93, by decide⟩ : Fin 148)) (colE2 ⟨93, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨93, by decide⟩ : Fin 148))
        (colE1 ⟨93, by decide⟩ p (transLenTr ⟨93, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_93 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_93_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_93_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_93_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_93_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_93_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_93_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_93_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_93_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_93_20 hp j hj hq
  simp at hm

theorem pair_147_94 (p : Nat) (hp : p < (Q2.transData.getD 94 []).length)
    (hrep : (Q2.cosetIsRep.getD 94 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨94, by decide⟩ : Fin 148)) (colE2 ⟨94, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨94, by decide⟩ : Fin 148))
        (colE1 ⟨94, by decide⟩ p (transLenTr ⟨94, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_94 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_94_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_94_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_94_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_94_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_94_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_94_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_94_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_94_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_94_20 hp j hj hq
  simp at hm

theorem pair_147_95 (p : Nat) (hp : p < (Q2.transData.getD 95 []).length)
    (hrep : (Q2.cosetIsRep.getD 95 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ p (transLenTr ⟨95, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_95 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_95_100 hp j hj hq
  simp at hm

theorem pair_147_96 (p : Nat) (hp : p < (Q2.transData.getD 96 []).length)
    (hrep : (Q2.cosetIsRep.getD 96 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ p (transLenTr ⟨96, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_96 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_96_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_96_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_96_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_96_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_96_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_96_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_96_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_96_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_96_20 hp j hj hq
  simp at hm

theorem pair_147_97 (p : Nat) (hp : p < (Q2.transData.getD 97 []).length)
    (hrep : (Q2.cosetIsRep.getD 97 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ p (transLenTr ⟨97, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_97 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_97_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_97_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_97_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_97_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_97_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_97_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_97_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_97_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_97_20 hp j hj hq
  simp at hm

theorem pair_147_98 (p : Nat) (hp : p < (Q2.transData.getD 98 []).length)
    (hrep : (Q2.cosetIsRep.getD 98 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ p (transLenTr ⟨98, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_98 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_98_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_98_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_98_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_98_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_98_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_98_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_98_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_98_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_98_20 hp j hj hq
  simp at hm

theorem pair_147_99 (p : Nat) (hp : p < (Q2.transData.getD 99 []).length)
    (hrep : (Q2.cosetIsRep.getD 99 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ p (transLenTr ⟨99, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_99 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_99_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_99_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_99_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_99_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_99_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_99_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_99_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_99_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_99_20 hp j hj hq
  simp at hm

theorem pair_147_100 (p : Nat) (hp : p < (Q2.transData.getD 100 []).length)
    (hrep : (Q2.cosetIsRep.getD 100 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ p (transLenTr ⟨100, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_100 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_100_100 hp j hj hq
  simp at hm

theorem pair_147_101 (p : Nat) (hp : p < (Q2.transData.getD 101 []).length)
    (hrep : (Q2.cosetIsRep.getD 101 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ p (transLenTr ⟨101, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_101 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_101_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_101_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_101_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_101_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_101_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_101_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_101_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_101_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_101_20 hp j hj hq
  simp at hm

theorem pair_147_102 (p : Nat) (hp : p < (Q2.transData.getD 102 []).length)
    (hrep : (Q2.cosetIsRep.getD 102 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ p (transLenTr ⟨102, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_102 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_102_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_102_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_102_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_102_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_102_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_102_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_102_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_102_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_102_20 hp j hj hq
  simp at hm

theorem pair_147_103 (p : Nat) (hp : p < (Q2.transData.getD 103 []).length)
    (hrep : (Q2.cosetIsRep.getD 103 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ p (transLenTr ⟨103, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_103 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_103_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_103_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_103_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_103_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_103_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_103_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_103_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_103_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_103_20 hp j hj hq
  simp at hm

theorem pair_147_104 (p : Nat) (hp : p < (Q2.transData.getD 104 []).length)
    (hrep : (Q2.cosetIsRep.getD 104 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ p (transLenTr ⟨104, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_104 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_104_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_104_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_104_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_104_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_104_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_104_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_104_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_104_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_104_20 hp j hj hq
  simp at hm

theorem pair_147_105 (p : Nat) (hp : p < (Q2.transData.getD 105 []).length)
    (hrep : (Q2.cosetIsRep.getD 105 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ p (transLenTr ⟨105, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_105 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_105_100 hp j hj hq
  simp at hm

theorem pair_147_106 (p : Nat) (hp : p < (Q2.transData.getD 106 []).length)
    (hrep : (Q2.cosetIsRep.getD 106 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ p (transLenTr ⟨106, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_106 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_106_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_106_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_106_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_106_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_106_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_106_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_106_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_106_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_106_20 hp j hj hq
  simp at hm

theorem pair_147_107 (p : Nat) (hp : p < (Q2.transData.getD 107 []).length)
    (hrep : (Q2.cosetIsRep.getD 107 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨107, by decide⟩ : Fin 148)) (colE2 ⟨107, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨107, by decide⟩ : Fin 148))
        (colE1 ⟨107, by decide⟩ p (transLenTr ⟨107, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_107 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_107_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_107_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_107_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_107_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_107_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_107_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_107_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_107_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_107_20 hp j hj hq
  simp at hm

theorem pair_147_108 (p : Nat) (hp : p < (Q2.transData.getD 108 []).length)
    (hrep : (Q2.cosetIsRep.getD 108 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨108, by decide⟩ : Fin 148)) (colE2 ⟨108, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨108, by decide⟩ : Fin 148))
        (colE1 ⟨108, by decide⟩ p (transLenTr ⟨108, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_108 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_108_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_108_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_108_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_108_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_108_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_108_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_108_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_108_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_108_20 hp j hj hq
  simp at hm

theorem pair_147_109 (p : Nat) (hp : p < (Q2.transData.getD 109 []).length)
    (hrep : (Q2.cosetIsRep.getD 109 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨109, by decide⟩ : Fin 148)) (colE2 ⟨109, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨109, by decide⟩ : Fin 148))
        (colE1 ⟨109, by decide⟩ p (transLenTr ⟨109, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_109 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_109_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_109_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_109_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_109_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_109_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_109_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_109_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_109_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_109_20 hp j hj hq
  simp at hm

theorem pair_147_110 (p : Nat) (hp : p < (Q2.transData.getD 110 []).length)
    (hrep : (Q2.cosetIsRep.getD 110 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨110, by decide⟩ : Fin 148)) (colE2 ⟨110, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨110, by decide⟩ : Fin 148))
        (colE1 ⟨110, by decide⟩ p (transLenTr ⟨110, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_110 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_110_100 hp j hj hq
  simp at hm

theorem pair_147_111 (p : Nat) (hp : p < (Q2.transData.getD 111 []).length)
    (hrep : (Q2.cosetIsRep.getD 111 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ p (transLenTr ⟨111, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_111 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_111_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_111_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_111_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_111_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_111_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_111_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_111_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_111_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_111_20 hp j hj hq
  simp at hm

theorem pair_147_112 (p : Nat) (hp : p < (Q2.transData.getD 112 []).length)
    (hrep : (Q2.cosetIsRep.getD 112 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨112, by decide⟩ : Fin 148)) (colE2 ⟨112, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨112, by decide⟩ : Fin 148))
        (colE1 ⟨112, by decide⟩ p (transLenTr ⟨112, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_112 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_112_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_112_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_112_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_112_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_112_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_112_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_112_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_112_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_112_20 hp j hj hq
  simp at hm

theorem pair_147_113 (p : Nat) (hp : p < (Q2.transData.getD 113 []).length)
    (hrep : (Q2.cosetIsRep.getD 113 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ p (transLenTr ⟨113, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_113 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_113_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_113_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_113_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_113_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_113_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_113_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_113_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_113_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_113_20 hp j hj hq
  simp at hm

theorem pair_147_114 (p : Nat) (hp : p < (Q2.transData.getD 114 []).length)
    (hrep : (Q2.cosetIsRep.getD 114 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ p (transLenTr ⟨114, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_114 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_114_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_114_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_114_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_114_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_114_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_114_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_114_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_114_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_114_20 hp j hj hq
  simp at hm

theorem pair_147_115 (p : Nat) (hp : p < (Q2.transData.getD 115 []).length)
    (hrep : (Q2.cosetIsRep.getD 115 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨115, by decide⟩ : Fin 148)) (colE2 ⟨115, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨115, by decide⟩ : Fin 148))
        (colE1 ⟨115, by decide⟩ p (transLenTr ⟨115, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_115 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_115_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_115_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_115_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_115_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_115_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_115_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_115_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_115_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_115_20 hp j hj hq
  simp at hm

theorem pair_147_116 (p : Nat) (hp : p < (Q2.transData.getD 116 []).length)
    (hrep : (Q2.cosetIsRep.getD 116 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨116, by decide⟩ : Fin 148)) (colE2 ⟨116, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨116, by decide⟩ : Fin 148))
        (colE1 ⟨116, by decide⟩ p (transLenTr ⟨116, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_116 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_116_120 hp j hj hq
  simp at hm

theorem pair_147_117 (p : Nat) (hp : p < (Q2.transData.getD 117 []).length)
    (hrep : (Q2.cosetIsRep.getD 117 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ p (transLenTr ⟨117, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_117 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_117_120 hp j hj hq
  simp at hm

theorem pair_147_118 (p : Nat) (hp : p < (Q2.transData.getD 118 []).length)
    (hrep : (Q2.cosetIsRep.getD 118 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ p (transLenTr ⟨118, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_118 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_118_120 hp j hj hq
  simp at hm

theorem pair_147_119 (p : Nat) (hp : p < (Q2.transData.getD 119 []).length)
    (hrep : (Q2.cosetIsRep.getD 119 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨119, by decide⟩ : Fin 148)) (colE2 ⟨119, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨119, by decide⟩ : Fin 148))
        (colE1 ⟨119, by decide⟩ p (transLenTr ⟨119, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_119 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_119_120 hp j hj hq
  simp at hm

theorem pair_147_120 (p : Nat) (hp : p < (Q2.transData.getD 120 []).length)
    (hrep : (Q2.cosetIsRep.getD 120 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨120, by decide⟩ : Fin 148)) (colE2 ⟨120, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨120, by decide⟩ : Fin 148))
        (colE1 ⟨120, by decide⟩ p (transLenTr ⟨120, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_120 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_120_120 hp j hj hq
  simp at hm

theorem pair_147_121 (p : Nat) (hp : p < (Q2.transData.getD 121 []).length)
    (hrep : (Q2.cosetIsRep.getD 121 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨121, by decide⟩ : Fin 148)) (colE2 ⟨121, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨121, by decide⟩ : Fin 148))
        (colE1 ⟨121, by decide⟩ p (transLenTr ⟨121, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_121 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_121_24 hp j hj hq
  simp at hm

theorem pair_147_122 (p : Nat) (hp : p < (Q2.transData.getD 122 []).length)
    (hrep : (Q2.cosetIsRep.getD 122 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨122, by decide⟩ : Fin 148)) (colE2 ⟨122, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨122, by decide⟩ : Fin 148))
        (colE1 ⟨122, by decide⟩ p (transLenTr ⟨122, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_122 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_122_24 hp j hj hq
  simp at hm

theorem pair_147_123 (p : Nat) (hp : p < (Q2.transData.getD 123 []).length)
    (hrep : (Q2.cosetIsRep.getD 123 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨123, by decide⟩ : Fin 148)) (colE2 ⟨123, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨123, by decide⟩ : Fin 148))
        (colE1 ⟨123, by decide⟩ p (transLenTr ⟨123, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_123 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_123_24 hp j hj hq
  simp at hm

theorem pair_147_124 (p : Nat) (hp : p < (Q2.transData.getD 124 []).length)
    (hrep : (Q2.cosetIsRep.getD 124 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨124, by decide⟩ : Fin 148)) (colE2 ⟨124, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨124, by decide⟩ : Fin 148))
        (colE1 ⟨124, by decide⟩ p (transLenTr ⟨124, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_124 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_124_24 hp j hj hq
  simp at hm

theorem pair_147_125 (p : Nat) (hp : p < (Q2.transData.getD 125 []).length)
    (hrep : (Q2.cosetIsRep.getD 125 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨125, by decide⟩ : Fin 148)) (colE2 ⟨125, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨125, by decide⟩ : Fin 148))
        (colE1 ⟨125, by decide⟩ p (transLenTr ⟨125, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_125 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_125_24 hp j hj hq
  simp at hm

theorem pair_147_126 (p : Nat) (hp : p < (Q2.transData.getD 126 []).length)
    (hrep : (Q2.cosetIsRep.getD 126 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨126, by decide⟩ : Fin 148)) (colE2 ⟨126, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨126, by decide⟩ : Fin 148))
        (colE1 ⟨126, by decide⟩ p (transLenTr ⟨126, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_126 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_126_24 hp j hj hq
  simp at hm

theorem pair_147_127 (p : Nat) (hp : p < (Q2.transData.getD 127 []).length)
    (hrep : (Q2.cosetIsRep.getD 127 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨127, by decide⟩ : Fin 148)) (colE2 ⟨127, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨127, by decide⟩ : Fin 148))
        (colE1 ⟨127, by decide⟩ p (transLenTr ⟨127, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_127 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_127_24 hp j hj hq
  simp at hm

theorem pair_147_128 (p : Nat) (hp : p < (Q2.transData.getD 128 []).length)
    (hrep : (Q2.cosetIsRep.getD 128 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨128, by decide⟩ : Fin 148)) (colE2 ⟨128, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨128, by decide⟩ : Fin 148))
        (colE1 ⟨128, by decide⟩ p (transLenTr ⟨128, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_128 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_128_24 hp j hj hq
  simp at hm

theorem pair_147_129 (p : Nat) (hp : p < (Q2.transData.getD 129 []).length)
    (hrep : (Q2.cosetIsRep.getD 129 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ p (transLenTr ⟨129, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_129 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_129_24 hp j hj hq
  simp at hm

theorem pair_147_130 (p : Nat) (hp : p < (Q2.transData.getD 130 []).length)
    (hrep : (Q2.cosetIsRep.getD 130 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ p (transLenTr ⟨130, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_130 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_130_24 hp j hj hq
  simp at hm

theorem pair_147_131 (p : Nat) (hp : p < (Q2.transData.getD 131 []).length)
    (hrep : (Q2.cosetIsRep.getD 131 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨131, by decide⟩ : Fin 148)) (colE2 ⟨131, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨131, by decide⟩ : Fin 148))
        (colE1 ⟨131, by decide⟩ p (transLenTr ⟨131, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_131 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_131_24 hp j hj hq
  simp at hm

theorem pair_147_132 (p : Nat) (hp : p < (Q2.transData.getD 132 []).length)
    (hrep : (Q2.cosetIsRep.getD 132 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨132, by decide⟩ : Fin 148)) (colE2 ⟨132, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨132, by decide⟩ : Fin 148))
        (colE1 ⟨132, by decide⟩ p (transLenTr ⟨132, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_132 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_132_24 hp j hj hq
  simp at hm

theorem pair_147_133 (p : Nat) (hp : p < (Q2.transData.getD 133 []).length)
    (hrep : (Q2.cosetIsRep.getD 133 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨133, by decide⟩ : Fin 148)) (colE2 ⟨133, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨133, by decide⟩ : Fin 148))
        (colE1 ⟨133, by decide⟩ p (transLenTr ⟨133, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_133 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_133_24 hp j hj hq
  simp at hm

theorem pair_147_134 (p : Nat) (hp : p < (Q2.transData.getD 134 []).length)
    (hrep : (Q2.cosetIsRep.getD 134 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ p (transLenTr ⟨134, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_134 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_134_24 hp j hj hq
  simp at hm

theorem pair_147_135 (p : Nat) (hp : p < (Q2.transData.getD 135 []).length)
    (hrep : (Q2.cosetIsRep.getD 135 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨135, by decide⟩ : Fin 148)) (colE2 ⟨135, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨135, by decide⟩ : Fin 148))
        (colE1 ⟨135, by decide⟩ p (transLenTr ⟨135, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_135 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_135_24 hp j hj hq
  simp at hm

theorem pair_147_136 (p : Nat) (hp : p < (Q2.transData.getD 136 []).length)
    (hrep : (Q2.cosetIsRep.getD 136 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨136, by decide⟩ : Fin 148)) (colE2 ⟨136, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨136, by decide⟩ : Fin 148))
        (colE1 ⟨136, by decide⟩ p (transLenTr ⟨136, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_136 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_136_24 hp j hj hq
  simp at hm

theorem pair_147_137 (p : Nat) (hp : p < (Q2.transData.getD 137 []).length)
    (hrep : (Q2.cosetIsRep.getD 137 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨137, by decide⟩ : Fin 148)) (colE2 ⟨137, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨137, by decide⟩ : Fin 148))
        (colE1 ⟨137, by decide⟩ p (transLenTr ⟨137, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_137 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_137_24 hp j hj hq
  simp at hm

theorem pair_147_138 (p : Nat) (hp : p < (Q2.transData.getD 138 []).length)
    (hrep : (Q2.cosetIsRep.getD 138 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨138, by decide⟩ : Fin 148)) (colE2 ⟨138, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨138, by decide⟩ : Fin 148))
        (colE1 ⟨138, by decide⟩ p (transLenTr ⟨138, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_138 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_138_24 hp j hj hq
  simp at hm

theorem pair_147_139 (p : Nat) (hp : p < (Q2.transData.getD 139 []).length)
    (hrep : (Q2.cosetIsRep.getD 139 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨139, by decide⟩ : Fin 148)) (colE2 ⟨139, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨139, by decide⟩ : Fin 148))
        (colE1 ⟨139, by decide⟩ p (transLenTr ⟨139, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_139 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_139_24 hp j hj hq
  simp at hm

theorem pair_147_140 (p : Nat) (hp : p < (Q2.transData.getD 140 []).length)
    (hrep : (Q2.cosetIsRep.getD 140 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨140, by decide⟩ : Fin 148)) (colE2 ⟨140, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨140, by decide⟩ : Fin 148))
        (colE1 ⟨140, by decide⟩ p (transLenTr ⟨140, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_140 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_140_24 hp j hj hq
  simp at hm

theorem pair_147_141 (p : Nat) (hp : p < (Q2.transData.getD 141 []).length)
    (hrep : (Q2.cosetIsRep.getD 141 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨141, by decide⟩ : Fin 148)) (colE2 ⟨141, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨141, by decide⟩ : Fin 148))
        (colE1 ⟨141, by decide⟩ p (transLenTr ⟨141, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_141 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_141_120 hp j hj hq
  simp at hm

theorem pair_147_142 (p : Nat) (hp : p < (Q2.transData.getD 142 []).length)
    (hrep : (Q2.cosetIsRep.getD 142 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨142, by decide⟩ : Fin 148)) (colE2 ⟨142, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨142, by decide⟩ : Fin 148))
        (colE1 ⟨142, by decide⟩ p (transLenTr ⟨142, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_142 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_142_24 hp j hj hq
  simp at hm

theorem pair_147_143 (p : Nat) (hp : p < (Q2.transData.getD 143 []).length)
    (hrep : (Q2.cosetIsRep.getD 143 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨143, by decide⟩ : Fin 148)) (colE2 ⟨143, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨143, by decide⟩ : Fin 148))
        (colE1 ⟨143, by decide⟩ p (transLenTr ⟨143, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_143 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_143_24 hp j hj hq
  simp at hm

theorem pair_147_144 (p : Nat) (hp : p < (Q2.transData.getD 144 []).length)
    (hrep : (Q2.cosetIsRep.getD 144 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨144, by decide⟩ : Fin 148)) (colE2 ⟨144, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨144, by decide⟩ : Fin 148))
        (colE1 ⟨144, by decide⟩ p (transLenTr ⟨144, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_144 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_144_24 hp j hj hq
  simp at hm

theorem pair_147_145 (p : Nat) (hp : p < (Q2.transData.getD 145 []).length)
    (hrep : (Q2.cosetIsRep.getD 145 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨145, by decide⟩ : Fin 148)) (colE2 ⟨145, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨145, by decide⟩ : Fin 148))
        (colE1 ⟨145, by decide⟩ p (transLenTr ⟨145, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_145 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_145_24 hp j hj hq
  simp at hm

theorem pair_147_146 (p : Nat) (hp : p < (Q2.transData.getD 146 []).length)
    (hrep : (Q2.cosetIsRep.getD 146 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨146, by decide⟩ : Fin 148)) (colE2 ⟨146, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨146, by decide⟩ : Fin 148))
        (colE1 ⟨146, by decide⟩ p (transLenTr ⟨146, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_146 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_146_24 hp j hj hq
  simp at hm

theorem pair_147_147 (p : Nat) (hp : p < (Q2.transData.getD 147 []).length)
    (hrep : (Q2.cosetIsRep.getD 147 []).getD p false = true)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨147, by decide⟩ : Fin 148)) (colE2 ⟨147, by decide⟩ p hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨147, by decide⟩ : Fin 148))
        (colE1 ⟨147, by decide⟩ p (transLenTr ⟨147, by decide⟩ p hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  have hm := repPos_147 p hp hrep
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_0 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_1 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_2 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_3 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_4 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_5 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_6 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_7 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_8 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_9 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_10 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_11 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_12 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_13 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_14 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_15 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_16 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_17 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_18 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_19 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_20 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_21 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_22 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_23 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_24 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_25 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_26 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_27 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_28 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_29 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_30 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_31 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_32 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_33 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_34 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_35 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_36 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_37 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_38 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_39 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_40 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_41 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_42 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_43 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_44 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_45 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_46 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_47 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_48 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_49 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_50 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_51 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_52 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_53 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_54 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_55 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_56 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_57 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_58 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_59 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_60 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_61 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_62 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_63 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_64 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_65 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_66 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_67 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_68 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_69 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_70 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_71 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_72 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_73 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_74 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_75 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_76 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_77 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_78 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_79 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_80 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_81 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_82 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_83 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_84 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_85 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_86 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_87 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_88 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_89 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_90 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_91 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_92 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_93 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_94 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_95 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_96 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_97 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_98 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_99 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_100 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_101 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_102 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_103 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_104 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_105 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_106 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_107 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_108 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_109 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_110 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_111 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_112 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_113 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_114 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_115 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_116 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_117 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_118 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_119 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_120 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_121 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_122 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_123 hp j hj hq
  rcases List.mem_cons.mp hm with rfl | hm
  · exact leaf_147_147_124 hp j hj hq
  simp at hm

end LeanDring.P5Presentation
