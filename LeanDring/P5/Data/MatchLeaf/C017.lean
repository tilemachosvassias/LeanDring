/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C186
import LeanDring.P5.Data.ColRestCheap.C187
import LeanDring.P5.Data.ColRestCheap.C188
import LeanDring.P5.Data.ColRestCheap.C189
import LeanDring.P5.Data.ColRestCheap.C190
import LeanDring.P5.Data.EntryK.C020
import LeanDring.P5.Data.EntryK.C021
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore

/-! # Stage-5 leaves, chunk 16 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_87_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T87_23
      hfix87_23 hinj87_23 hcardT87_23
      (fun i => conj_mem_of_fixedPoints _ _ (T87_23 i) (hfix87_23 i) _)
      ⟨87, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T87_23_2 Q2.hfix87_23_2 Q2.hinj87_23_2
      Q2.hcardT87_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_23_2 i) (Q2.hfix87_23_2 i) _)
      colCert_87_23_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T87_23
      hfix87_23 hinj87_23 hcardT87_23
      (fun i => conj_mem_of_fixedPoints _ _ (T87_23 i) (hfix87_23 i) _)
      ⟨87, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T87_23_2 Q2.hfix87_23_2 Q2.hinj87_23_2
      Q2.hcardT87_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_23_2 i) (Q2.hfix87_23_2 i) _)
      colCert_87_23_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T87_23
      hfix87_23 hinj87_23 hcardT87_23
      (fun i => conj_mem_of_fixedPoints _ _ (T87_23 i) (hfix87_23 i) _)
      ⟨87, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T87_23_2 Q2.hfix87_23_2 Q2.hinj87_23_2
      Q2.hcardT87_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_23_2 i) (Q2.hfix87_23_2 i) _)
      colCert_87_23_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T87_23
      hfix87_23 hinj87_23 hcardT87_23
      (fun i => conj_mem_of_fixedPoints _ _ (T87_23 i) (hfix87_23 i) _)
      ⟨87, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T87_23_2 Q2.hfix87_23_2 Q2.hinj87_23_2
      Q2.hcardT87_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_23_2 i) (Q2.hfix87_23_2 i) _)
      colCert_87_23_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T87_23
      hfix87_23 hinj87_23 hcardT87_23
      (fun i => conj_mem_of_fixedPoints _ _ (T87_23 i) (hfix87_23 i) _)
      ⟨87, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T87_23_2 Q2.hfix87_23_2 Q2.hinj87_23_2
      Q2.hcardT87_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_23_2 i) (Q2.hfix87_23_2 i) _)
      colCert_87_23_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T87_23
      hfix87_23 hinj87_23 hcardT87_23
      (fun i => conj_mem_of_fixedPoints _ _ (T87_23 i) (hfix87_23 i) _)
      ⟨87, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T87_23_2 Q2.hfix87_23_2 Q2.hinj87_23_2
      Q2.hcardT87_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_23_2 i) (Q2.hfix87_23_2 i) _)
      colCert_87_23_5.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T87_23
      hfix87_23 hinj87_23 hcardT87_23
      (fun i => conj_mem_of_fixedPoints _ _ (T87_23 i) (hfix87_23 i) _)
      ⟨87, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T87_23_2 Q2.hfix87_23_2 Q2.hinj87_23_2
      Q2.hcardT87_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_23_2 i) (Q2.hfix87_23_2 i) _)
      colCert_87_23_10.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T87_23
      hfix87_23 hinj87_23 hcardT87_23
      (fun i => conj_mem_of_fixedPoints _ _ (T87_23 i) (hfix87_23 i) _)
      ⟨87, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T87_23_2 Q2.hfix87_23_2 Q2.hinj87_23_2
      Q2.hcardT87_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_23_2 i) (Q2.hfix87_23_2 i) _)
      colCert_87_23_15.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T87_23
      hfix87_23 hinj87_23 hcardT87_23
      (fun i => conj_mem_of_fixedPoints _ _ (T87_23 i) (hfix87_23 i) _)
      ⟨87, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T87_23_2 Q2.hfix87_23_2 Q2.hinj87_23_2
      Q2.hcardT87_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_23_2 i) (Q2.hfix87_23_2 i) _)
      colCert_87_23_20.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T87_25
      hfix87_25 hinj87_25 hcardT87_25
      (fun i => conj_mem_of_fixedPoints _ _ (T87_25 i) (hfix87_25 i) _)
      ⟨87, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T87_25_2 Q2.hfix87_25_2 Q2.hinj87_25_2
      Q2.hcardT87_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_25_2 i) (Q2.hfix87_25_2 i) _)
      colCert_87_25_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T87_25
      hfix87_25 hinj87_25 hcardT87_25
      (fun i => conj_mem_of_fixedPoints _ _ (T87_25 i) (hfix87_25 i) _)
      ⟨87, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T87_25_2 Q2.hfix87_25_2 Q2.hinj87_25_2
      Q2.hcardT87_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_25_2 i) (Q2.hfix87_25_2 i) _)
      colCert_87_25_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T87_25
      hfix87_25 hinj87_25 hcardT87_25
      (fun i => conj_mem_of_fixedPoints _ _ (T87_25 i) (hfix87_25 i) _)
      ⟨87, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T87_25_2 Q2.hfix87_25_2 Q2.hinj87_25_2
      Q2.hcardT87_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_25_2 i) (Q2.hfix87_25_2 i) _)
      colCert_87_25_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T87_25
      hfix87_25 hinj87_25 hcardT87_25
      (fun i => conj_mem_of_fixedPoints _ _ (T87_25 i) (hfix87_25 i) _)
      ⟨87, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T87_25_2 Q2.hfix87_25_2 Q2.hinj87_25_2
      Q2.hcardT87_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_25_2 i) (Q2.hfix87_25_2 i) _)
      colCert_87_25_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T87_25
      hfix87_25 hinj87_25 hcardT87_25
      (fun i => conj_mem_of_fixedPoints _ _ (T87_25 i) (hfix87_25 i) _)
      ⟨87, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T87_25_2 Q2.hfix87_25_2 Q2.hinj87_25_2
      Q2.hcardT87_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_25_2 i) (Q2.hfix87_25_2 i) _)
      colCert_87_25_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T87_25
      hfix87_25 hinj87_25 hcardT87_25
      (fun i => conj_mem_of_fixedPoints _ _ (T87_25 i) (hfix87_25 i) _)
      ⟨87, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T87_25_2 Q2.hfix87_25_2 Q2.hinj87_25_2
      Q2.hcardT87_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_25_2 i) (Q2.hfix87_25_2 i) _)
      colCert_87_25_5.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T87_25
      hfix87_25 hinj87_25 hcardT87_25
      (fun i => conj_mem_of_fixedPoints _ _ (T87_25 i) (hfix87_25 i) _)
      ⟨87, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T87_25_2 Q2.hfix87_25_2 Q2.hinj87_25_2
      Q2.hcardT87_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_25_2 i) (Q2.hfix87_25_2 i) _)
      colCert_87_25_10.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T87_25
      hfix87_25 hinj87_25 hcardT87_25
      (fun i => conj_mem_of_fixedPoints _ _ (T87_25 i) (hfix87_25 i) _)
      ⟨87, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T87_25_2 Q2.hfix87_25_2 Q2.hinj87_25_2
      Q2.hcardT87_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_25_2 i) (Q2.hfix87_25_2 i) _)
      colCert_87_25_15.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T87_25
      hfix87_25 hinj87_25 hcardT87_25
      (fun i => conj_mem_of_fixedPoints _ _ (T87_25 i) (hfix87_25 i) _)
      ⟨87, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T87_25_2 Q2.hfix87_25_2 Q2.hinj87_25_2
      Q2.hcardT87_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_25_2 i) (Q2.hfix87_25_2 i) _)
      colCert_87_25_20.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T87_54
      hfix87_54 hinj87_54 hcardT87_54
      (fun i => conj_mem_of_fixedPoints _ _ (T87_54 i) (hfix87_54 i) _)
      ⟨87, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T87_54_2 Q2.hfix87_54_2 Q2.hinj87_54_2
      Q2.hcardT87_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_54_2 i) (Q2.hfix87_54_2 i) _)
      colCert_87_54_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T87_54
      hfix87_54 hinj87_54 hcardT87_54
      (fun i => conj_mem_of_fixedPoints _ _ (T87_54 i) (hfix87_54 i) _)
      ⟨87, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T87_54_2 Q2.hfix87_54_2 Q2.hinj87_54_2
      Q2.hcardT87_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_54_2 i) (Q2.hfix87_54_2 i) _)
      colCert_87_54_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T87_54
      hfix87_54 hinj87_54 hcardT87_54
      (fun i => conj_mem_of_fixedPoints _ _ (T87_54 i) (hfix87_54 i) _)
      ⟨87, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T87_54_2 Q2.hfix87_54_2 Q2.hinj87_54_2
      Q2.hcardT87_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_54_2 i) (Q2.hfix87_54_2 i) _)
      colCert_87_54_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T87_54
      hfix87_54 hinj87_54 hcardT87_54
      (fun i => conj_mem_of_fixedPoints _ _ (T87_54 i) (hfix87_54 i) _)
      ⟨87, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T87_54_2 Q2.hfix87_54_2 Q2.hinj87_54_2
      Q2.hcardT87_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_54_2 i) (Q2.hfix87_54_2 i) _)
      colCert_87_54_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T87_54
      hfix87_54 hinj87_54 hcardT87_54
      (fun i => conj_mem_of_fixedPoints _ _ (T87_54 i) (hfix87_54 i) _)
      ⟨87, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T87_54_2 Q2.hfix87_54_2 Q2.hinj87_54_2
      Q2.hcardT87_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_54_2 i) (Q2.hfix87_54_2 i) _)
      colCert_87_54_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T87_54
      hfix87_54 hinj87_54 hcardT87_54
      (fun i => conj_mem_of_fixedPoints _ _ (T87_54 i) (hfix87_54 i) _)
      ⟨87, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T87_54_2 Q2.hfix87_54_2 Q2.hinj87_54_2
      Q2.hcardT87_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_54_2 i) (Q2.hfix87_54_2 i) _)
      colCert_87_54_5.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T87_54
      hfix87_54 hinj87_54 hcardT87_54
      (fun i => conj_mem_of_fixedPoints _ _ (T87_54 i) (hfix87_54 i) _)
      ⟨87, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T87_54_2 Q2.hfix87_54_2 Q2.hinj87_54_2
      Q2.hcardT87_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_54_2 i) (Q2.hfix87_54_2 i) _)
      colCert_87_54_10.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T87_54
      hfix87_54 hinj87_54 hcardT87_54
      (fun i => conj_mem_of_fixedPoints _ _ (T87_54 i) (hfix87_54 i) _)
      ⟨87, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T87_54_2 Q2.hfix87_54_2 Q2.hinj87_54_2
      Q2.hcardT87_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_54_2 i) (Q2.hfix87_54_2 i) _)
      colCert_87_54_15.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T87_54
      hfix87_54 hinj87_54 hcardT87_54
      (fun i => conj_mem_of_fixedPoints _ _ (T87_54 i) (hfix87_54 i) _)
      ⟨87, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T87_54_2 Q2.hfix87_54_2 Q2.hinj87_54_2
      Q2.hcardT87_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_54_2 i) (Q2.hfix87_54_2 i) _)
      colCert_87_54_20.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_0 (hp : 0 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 0 (transLenTr ⟨87, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 0 (transLenTr ⟨87, by decide⟩ 0 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 0 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_1 (hp : 1 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 1 (transLenTr ⟨87, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 1 (transLenTr ⟨87, by decide⟩ 1 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 1 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_2 (hp : 2 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 2 (transLenTr ⟨87, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 2 (transLenTr ⟨87, by decide⟩ 2 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 2 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_3 (hp : 3 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 3 (transLenTr ⟨87, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 3 (transLenTr ⟨87, by decide⟩ 3 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 3 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_4 (hp : 4 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 4 (transLenTr ⟨87, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 4 (transLenTr ⟨87, by decide⟩ 4 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 4 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_5 (hp : 5 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 5 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 5 (transLenTr ⟨87, by decide⟩ 5 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 5 (transLenTr ⟨87, by decide⟩ 5 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 5 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_5.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_6 (hp : 6 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 6 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 6 (transLenTr ⟨87, by decide⟩ 6 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 6 (transLenTr ⟨87, by decide⟩ 6 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 6 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_6.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_7 (hp : 7 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 7 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 7 (transLenTr ⟨87, by decide⟩ 7 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 7 (transLenTr ⟨87, by decide⟩ 7 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 7 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_7.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_8 (hp : 8 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 8 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 8 (transLenTr ⟨87, by decide⟩ 8 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 8 (transLenTr ⟨87, by decide⟩ 8 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 8 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_8.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_9 (hp : 9 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 9 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 9 (transLenTr ⟨87, by decide⟩ 9 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 9 (transLenTr ⟨87, by decide⟩ 9 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 9 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_9.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_10 (hp : 10 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 10 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 10 (transLenTr ⟨87, by decide⟩ 10 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 10 (transLenTr ⟨87, by decide⟩ 10 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 10 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_10.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_11 (hp : 11 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 11 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 11 (transLenTr ⟨87, by decide⟩ 11 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 11 (transLenTr ⟨87, by decide⟩ 11 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 11 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_11.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_12 (hp : 12 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 12 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 12 (transLenTr ⟨87, by decide⟩ 12 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 12 (transLenTr ⟨87, by decide⟩ 12 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 12 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_12.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_13 (hp : 13 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 13 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 13 (transLenTr ⟨87, by decide⟩ 13 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 13 (transLenTr ⟨87, by decide⟩ 13 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 13 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_13.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_14 (hp : 14 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 14 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 14 (transLenTr ⟨87, by decide⟩ 14 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 14 (transLenTr ⟨87, by decide⟩ 14 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 14 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_14.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_15 (hp : 15 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 15 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 15 (transLenTr ⟨87, by decide⟩ 15 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 15 (transLenTr ⟨87, by decide⟩ 15 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 15 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_15.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_16 (hp : 16 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 16 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 16 (transLenTr ⟨87, by decide⟩ 16 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 16 (transLenTr ⟨87, by decide⟩ 16 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 16 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_16.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_17 (hp : 17 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 17 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 17 (transLenTr ⟨87, by decide⟩ 17 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 17 (transLenTr ⟨87, by decide⟩ 17 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 17 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_17.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_18 (hp : 18 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 18 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 18 (transLenTr ⟨87, by decide⟩ 18 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 18 (transLenTr ⟨87, by decide⟩ 18 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 18 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_18.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_19 (hp : 19 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 19 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 19 (transLenTr ⟨87, by decide⟩ 19 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 19 (transLenTr ⟨87, by decide⟩ 19 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 19 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_19.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_20 (hp : 20 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 20 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 20 (transLenTr ⟨87, by decide⟩ 20 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 20 (transLenTr ⟨87, by decide⟩ 20 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 20 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_20.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_21 (hp : 21 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 21 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 21 (transLenTr ⟨87, by decide⟩ 21 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 21 (transLenTr ⟨87, by decide⟩ 21 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 21 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_21.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_22 (hp : 22 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 22 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 22 (transLenTr ⟨87, by decide⟩ 22 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 22 (transLenTr ⟨87, by decide⟩ 22 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 22 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_22.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_23 (hp : 23 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 23 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 23 (transLenTr ⟨87, by decide⟩ 23 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 23 (transLenTr ⟨87, by decide⟩ 23 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 23 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_23.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_87_24 (hp : 24 < (Q2.transData.getD 87 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨87, by decide⟩ : Fin 148)) (colE2 ⟨87, by decide⟩ 24 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨87, by decide⟩ : Fin 148))
        (colE1 ⟨87, by decide⟩ 24 (transLenTr ⟨87, by decide⟩ 24 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨87, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨87, by decide⟩ 24 (transLenTr ⟨87, by decide⟩ 24 hp)) T87_87
      hfix87_87 hinj87_87 hcardT87_87
      (fun i => conj_mem_of_fixedPoints _ _ (T87_87 i) (hfix87_87 i) _)
      ⟨87, by decide⟩ ⟨87, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨87, by decide⟩ 24 hp) Q2.T87_87_2 Q2.hfix87_87_2 Q2.hinj87_87_2
      Q2.hcardT87_87_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_87_2 i) (Q2.hfix87_87_2 i) _)
      colCert_87_87_24.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_88_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T88_2
      hfix88_2 hinj88_2 hcardT88_2
      (fun i => conj_mem_of_fixedPoints _ _ (T88_2 i) (hfix88_2 i) _)
      ⟨88, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T88_2_2 Q2.hfix88_2_2 Q2.hinj88_2_2
      Q2.hcardT88_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_2_2 i) (Q2.hfix88_2_2 i) _)
      colCert_88_2_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T88_2
      hfix88_2 hinj88_2 hcardT88_2
      (fun i => conj_mem_of_fixedPoints _ _ (T88_2 i) (hfix88_2 i) _)
      ⟨88, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T88_2_2 Q2.hfix88_2_2 Q2.hinj88_2_2
      Q2.hcardT88_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_2_2 i) (Q2.hfix88_2_2 i) _)
      colCert_88_2_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T88_2
      hfix88_2 hinj88_2 hcardT88_2
      (fun i => conj_mem_of_fixedPoints _ _ (T88_2 i) (hfix88_2 i) _)
      ⟨88, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T88_2_2 Q2.hfix88_2_2 Q2.hinj88_2_2
      Q2.hcardT88_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_2_2 i) (Q2.hfix88_2_2 i) _)
      colCert_88_2_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T88_2
      hfix88_2 hinj88_2 hcardT88_2
      (fun i => conj_mem_of_fixedPoints _ _ (T88_2 i) (hfix88_2 i) _)
      ⟨88, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T88_2_2 Q2.hfix88_2_2 Q2.hinj88_2_2
      Q2.hcardT88_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_2_2 i) (Q2.hfix88_2_2 i) _)
      colCert_88_2_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T88_2
      hfix88_2 hinj88_2 hcardT88_2
      (fun i => conj_mem_of_fixedPoints _ _ (T88_2 i) (hfix88_2 i) _)
      ⟨88, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T88_2_2 Q2.hfix88_2_2 Q2.hinj88_2_2
      Q2.hcardT88_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_2_2 i) (Q2.hfix88_2_2 i) _)
      colCert_88_2_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T88_3
      hfix88_3 hinj88_3 hcardT88_3
      (fun i => conj_mem_of_fixedPoints _ _ (T88_3 i) (hfix88_3 i) _)
      ⟨88, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T88_3_2 Q2.hfix88_3_2 Q2.hinj88_3_2
      Q2.hcardT88_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_3_2 i) (Q2.hfix88_3_2 i) _)
      colCert_88_3_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T88_3
      hfix88_3 hinj88_3 hcardT88_3
      (fun i => conj_mem_of_fixedPoints _ _ (T88_3 i) (hfix88_3 i) _)
      ⟨88, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T88_3_2 Q2.hfix88_3_2 Q2.hinj88_3_2
      Q2.hcardT88_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_3_2 i) (Q2.hfix88_3_2 i) _)
      colCert_88_3_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T88_3
      hfix88_3 hinj88_3 hcardT88_3
      (fun i => conj_mem_of_fixedPoints _ _ (T88_3 i) (hfix88_3 i) _)
      ⟨88, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T88_3_2 Q2.hfix88_3_2 Q2.hinj88_3_2
      Q2.hcardT88_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_3_2 i) (Q2.hfix88_3_2 i) _)
      colCert_88_3_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T88_3
      hfix88_3 hinj88_3 hcardT88_3
      (fun i => conj_mem_of_fixedPoints _ _ (T88_3 i) (hfix88_3 i) _)
      ⟨88, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T88_3_2 Q2.hfix88_3_2 Q2.hinj88_3_2
      Q2.hcardT88_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_3_2 i) (Q2.hfix88_3_2 i) _)
      colCert_88_3_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T88_3
      hfix88_3 hinj88_3 hcardT88_3
      (fun i => conj_mem_of_fixedPoints _ _ (T88_3 i) (hfix88_3 i) _)
      ⟨88, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T88_3_2 Q2.hfix88_3_2 Q2.hinj88_3_2
      Q2.hcardT88_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_3_2 i) (Q2.hfix88_3_2 i) _)
      colCert_88_3_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T88_4
      hfix88_4 hinj88_4 hcardT88_4
      (fun i => conj_mem_of_fixedPoints _ _ (T88_4 i) (hfix88_4 i) _)
      ⟨88, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T88_4_2 Q2.hfix88_4_2 Q2.hinj88_4_2
      Q2.hcardT88_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_4_2 i) (Q2.hfix88_4_2 i) _)
      colCert_88_4_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T88_4
      hfix88_4 hinj88_4 hcardT88_4
      (fun i => conj_mem_of_fixedPoints _ _ (T88_4 i) (hfix88_4 i) _)
      ⟨88, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T88_4_2 Q2.hfix88_4_2 Q2.hinj88_4_2
      Q2.hcardT88_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_4_2 i) (Q2.hfix88_4_2 i) _)
      colCert_88_4_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T88_4
      hfix88_4 hinj88_4 hcardT88_4
      (fun i => conj_mem_of_fixedPoints _ _ (T88_4 i) (hfix88_4 i) _)
      ⟨88, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T88_4_2 Q2.hfix88_4_2 Q2.hinj88_4_2
      Q2.hcardT88_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_4_2 i) (Q2.hfix88_4_2 i) _)
      colCert_88_4_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T88_4
      hfix88_4 hinj88_4 hcardT88_4
      (fun i => conj_mem_of_fixedPoints _ _ (T88_4 i) (hfix88_4 i) _)
      ⟨88, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T88_4_2 Q2.hfix88_4_2 Q2.hinj88_4_2
      Q2.hcardT88_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_4_2 i) (Q2.hfix88_4_2 i) _)
      colCert_88_4_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T88_4
      hfix88_4 hinj88_4 hcardT88_4
      (fun i => conj_mem_of_fixedPoints _ _ (T88_4 i) (hfix88_4 i) _)
      ⟨88, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T88_4_2 Q2.hfix88_4_2 Q2.hinj88_4_2
      Q2.hcardT88_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_4_2 i) (Q2.hfix88_4_2 i) _)
      colCert_88_4_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T88_5
      hfix88_5 hinj88_5 hcardT88_5
      (fun i => conj_mem_of_fixedPoints _ _ (T88_5 i) (hfix88_5 i) _)
      ⟨88, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T88_5_2 Q2.hfix88_5_2 Q2.hinj88_5_2
      Q2.hcardT88_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_5_2 i) (Q2.hfix88_5_2 i) _)
      colCert_88_5_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T88_5
      hfix88_5 hinj88_5 hcardT88_5
      (fun i => conj_mem_of_fixedPoints _ _ (T88_5 i) (hfix88_5 i) _)
      ⟨88, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T88_5_2 Q2.hfix88_5_2 Q2.hinj88_5_2
      Q2.hcardT88_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_5_2 i) (Q2.hfix88_5_2 i) _)
      colCert_88_5_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T88_5
      hfix88_5 hinj88_5 hcardT88_5
      (fun i => conj_mem_of_fixedPoints _ _ (T88_5 i) (hfix88_5 i) _)
      ⟨88, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T88_5_2 Q2.hfix88_5_2 Q2.hinj88_5_2
      Q2.hcardT88_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_5_2 i) (Q2.hfix88_5_2 i) _)
      colCert_88_5_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T88_5
      hfix88_5 hinj88_5 hcardT88_5
      (fun i => conj_mem_of_fixedPoints _ _ (T88_5 i) (hfix88_5 i) _)
      ⟨88, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T88_5_2 Q2.hfix88_5_2 Q2.hinj88_5_2
      Q2.hcardT88_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_5_2 i) (Q2.hfix88_5_2 i) _)
      colCert_88_5_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T88_5
      hfix88_5 hinj88_5 hcardT88_5
      (fun i => conj_mem_of_fixedPoints _ _ (T88_5 i) (hfix88_5 i) _)
      ⟨88, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T88_5_2 Q2.hfix88_5_2 Q2.hinj88_5_2
      Q2.hcardT88_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_5_2 i) (Q2.hfix88_5_2 i) _)
      colCert_88_5_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T88_6
      hfix88_6 hinj88_6 hcardT88_6
      (fun i => conj_mem_of_fixedPoints _ _ (T88_6 i) (hfix88_6 i) _)
      ⟨88, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T88_6_2 Q2.hfix88_6_2 Q2.hinj88_6_2
      Q2.hcardT88_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_6_2 i) (Q2.hfix88_6_2 i) _)
      colCert_88_6_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T88_6
      hfix88_6 hinj88_6 hcardT88_6
      (fun i => conj_mem_of_fixedPoints _ _ (T88_6 i) (hfix88_6 i) _)
      ⟨88, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T88_6_2 Q2.hfix88_6_2 Q2.hinj88_6_2
      Q2.hcardT88_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_6_2 i) (Q2.hfix88_6_2 i) _)
      colCert_88_6_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T88_6
      hfix88_6 hinj88_6 hcardT88_6
      (fun i => conj_mem_of_fixedPoints _ _ (T88_6 i) (hfix88_6 i) _)
      ⟨88, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T88_6_2 Q2.hfix88_6_2 Q2.hinj88_6_2
      Q2.hcardT88_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_6_2 i) (Q2.hfix88_6_2 i) _)
      colCert_88_6_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T88_6
      hfix88_6 hinj88_6 hcardT88_6
      (fun i => conj_mem_of_fixedPoints _ _ (T88_6 i) (hfix88_6 i) _)
      ⟨88, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T88_6_2 Q2.hfix88_6_2 Q2.hinj88_6_2
      Q2.hcardT88_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_6_2 i) (Q2.hfix88_6_2 i) _)
      colCert_88_6_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T88_6
      hfix88_6 hinj88_6 hcardT88_6
      (fun i => conj_mem_of_fixedPoints _ _ (T88_6 i) (hfix88_6 i) _)
      ⟨88, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T88_6_2 Q2.hfix88_6_2 Q2.hinj88_6_2
      Q2.hcardT88_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_6_2 i) (Q2.hfix88_6_2 i) _)
      colCert_88_6_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T88_11
      hfix88_11 hinj88_11 hcardT88_11
      (fun i => conj_mem_of_fixedPoints _ _ (T88_11 i) (hfix88_11 i) _)
      ⟨88, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T88_11_2 Q2.hfix88_11_2 Q2.hinj88_11_2
      Q2.hcardT88_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_11_2 i) (Q2.hfix88_11_2 i) _)
      colCert_88_11_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T88_11
      hfix88_11 hinj88_11 hcardT88_11
      (fun i => conj_mem_of_fixedPoints _ _ (T88_11 i) (hfix88_11 i) _)
      ⟨88, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T88_11_2 Q2.hfix88_11_2 Q2.hinj88_11_2
      Q2.hcardT88_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_11_2 i) (Q2.hfix88_11_2 i) _)
      colCert_88_11_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T88_11
      hfix88_11 hinj88_11 hcardT88_11
      (fun i => conj_mem_of_fixedPoints _ _ (T88_11 i) (hfix88_11 i) _)
      ⟨88, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T88_11_2 Q2.hfix88_11_2 Q2.hinj88_11_2
      Q2.hcardT88_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_11_2 i) (Q2.hfix88_11_2 i) _)
      colCert_88_11_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T88_11
      hfix88_11 hinj88_11 hcardT88_11
      (fun i => conj_mem_of_fixedPoints _ _ (T88_11 i) (hfix88_11 i) _)
      ⟨88, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T88_11_2 Q2.hfix88_11_2 Q2.hinj88_11_2
      Q2.hcardT88_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_11_2 i) (Q2.hfix88_11_2 i) _)
      colCert_88_11_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T88_11
      hfix88_11 hinj88_11 hcardT88_11
      (fun i => conj_mem_of_fixedPoints _ _ (T88_11 i) (hfix88_11 i) _)
      ⟨88, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T88_11_2 Q2.hfix88_11_2 Q2.hinj88_11_2
      Q2.hcardT88_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_11_2 i) (Q2.hfix88_11_2 i) _)
      colCert_88_11_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T88_12
      hfix88_12 hinj88_12 hcardT88_12
      (fun i => conj_mem_of_fixedPoints _ _ (T88_12 i) (hfix88_12 i) _)
      ⟨88, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T88_12_2 Q2.hfix88_12_2 Q2.hinj88_12_2
      Q2.hcardT88_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_12_2 i) (Q2.hfix88_12_2 i) _)
      colCert_88_12_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T88_12
      hfix88_12 hinj88_12 hcardT88_12
      (fun i => conj_mem_of_fixedPoints _ _ (T88_12 i) (hfix88_12 i) _)
      ⟨88, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T88_12_2 Q2.hfix88_12_2 Q2.hinj88_12_2
      Q2.hcardT88_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_12_2 i) (Q2.hfix88_12_2 i) _)
      colCert_88_12_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T88_12
      hfix88_12 hinj88_12 hcardT88_12
      (fun i => conj_mem_of_fixedPoints _ _ (T88_12 i) (hfix88_12 i) _)
      ⟨88, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T88_12_2 Q2.hfix88_12_2 Q2.hinj88_12_2
      Q2.hcardT88_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_12_2 i) (Q2.hfix88_12_2 i) _)
      colCert_88_12_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T88_12
      hfix88_12 hinj88_12 hcardT88_12
      (fun i => conj_mem_of_fixedPoints _ _ (T88_12 i) (hfix88_12 i) _)
      ⟨88, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T88_12_2 Q2.hfix88_12_2 Q2.hinj88_12_2
      Q2.hcardT88_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_12_2 i) (Q2.hfix88_12_2 i) _)
      colCert_88_12_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T88_12
      hfix88_12 hinj88_12 hcardT88_12
      (fun i => conj_mem_of_fixedPoints _ _ (T88_12 i) (hfix88_12 i) _)
      ⟨88, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T88_12_2 Q2.hfix88_12_2 Q2.hinj88_12_2
      Q2.hcardT88_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_12_2 i) (Q2.hfix88_12_2 i) _)
      colCert_88_12_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T88_20
      hfix88_20 hinj88_20 hcardT88_20
      (fun i => conj_mem_of_fixedPoints _ _ (T88_20 i) (hfix88_20 i) _)
      ⟨88, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T88_20_2 Q2.hfix88_20_2 Q2.hinj88_20_2
      Q2.hcardT88_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_20_2 i) (Q2.hfix88_20_2 i) _)
      colCert_88_20_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T88_20
      hfix88_20 hinj88_20 hcardT88_20
      (fun i => conj_mem_of_fixedPoints _ _ (T88_20 i) (hfix88_20 i) _)
      ⟨88, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T88_20_2 Q2.hfix88_20_2 Q2.hinj88_20_2
      Q2.hcardT88_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_20_2 i) (Q2.hfix88_20_2 i) _)
      colCert_88_20_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T88_20
      hfix88_20 hinj88_20 hcardT88_20
      (fun i => conj_mem_of_fixedPoints _ _ (T88_20 i) (hfix88_20 i) _)
      ⟨88, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T88_20_2 Q2.hfix88_20_2 Q2.hinj88_20_2
      Q2.hcardT88_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_20_2 i) (Q2.hfix88_20_2 i) _)
      colCert_88_20_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T88_20
      hfix88_20 hinj88_20 hcardT88_20
      (fun i => conj_mem_of_fixedPoints _ _ (T88_20 i) (hfix88_20 i) _)
      ⟨88, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T88_20_2 Q2.hfix88_20_2 Q2.hinj88_20_2
      Q2.hcardT88_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_20_2 i) (Q2.hfix88_20_2 i) _)
      colCert_88_20_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T88_20
      hfix88_20 hinj88_20 hcardT88_20
      (fun i => conj_mem_of_fixedPoints _ _ (T88_20 i) (hfix88_20 i) _)
      ⟨88, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T88_20_2 Q2.hfix88_20_2 Q2.hinj88_20_2
      Q2.hcardT88_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_20_2 i) (Q2.hfix88_20_2 i) _)
      colCert_88_20_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T88_20
      hfix88_20 hinj88_20 hcardT88_20
      (fun i => conj_mem_of_fixedPoints _ _ (T88_20 i) (hfix88_20 i) _)
      ⟨88, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T88_20_2 Q2.hfix88_20_2 Q2.hinj88_20_2
      Q2.hcardT88_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_20_2 i) (Q2.hfix88_20_2 i) _)
      colCert_88_20_5.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T88_20
      hfix88_20 hinj88_20 hcardT88_20
      (fun i => conj_mem_of_fixedPoints _ _ (T88_20 i) (hfix88_20 i) _)
      ⟨88, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T88_20_2 Q2.hfix88_20_2 Q2.hinj88_20_2
      Q2.hcardT88_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_20_2 i) (Q2.hfix88_20_2 i) _)
      colCert_88_20_10.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T88_20
      hfix88_20 hinj88_20 hcardT88_20
      (fun i => conj_mem_of_fixedPoints _ _ (T88_20 i) (hfix88_20 i) _)
      ⟨88, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T88_20_2 Q2.hfix88_20_2 Q2.hinj88_20_2
      Q2.hcardT88_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_20_2 i) (Q2.hfix88_20_2 i) _)
      colCert_88_20_15.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T88_20
      hfix88_20 hinj88_20 hcardT88_20
      (fun i => conj_mem_of_fixedPoints _ _ (T88_20 i) (hfix88_20 i) _)
      ⟨88, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T88_20_2 Q2.hfix88_20_2 Q2.hinj88_20_2
      Q2.hcardT88_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_20_2 i) (Q2.hfix88_20_2 i) _)
      colCert_88_20_20.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T88_21
      hfix88_21 hinj88_21 hcardT88_21
      (fun i => conj_mem_of_fixedPoints _ _ (T88_21 i) (hfix88_21 i) _)
      ⟨88, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T88_21_2 Q2.hfix88_21_2 Q2.hinj88_21_2
      Q2.hcardT88_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_21_2 i) (Q2.hfix88_21_2 i) _)
      colCert_88_21_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T88_21
      hfix88_21 hinj88_21 hcardT88_21
      (fun i => conj_mem_of_fixedPoints _ _ (T88_21 i) (hfix88_21 i) _)
      ⟨88, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T88_21_2 Q2.hfix88_21_2 Q2.hinj88_21_2
      Q2.hcardT88_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_21_2 i) (Q2.hfix88_21_2 i) _)
      colCert_88_21_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T88_21
      hfix88_21 hinj88_21 hcardT88_21
      (fun i => conj_mem_of_fixedPoints _ _ (T88_21 i) (hfix88_21 i) _)
      ⟨88, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T88_21_2 Q2.hfix88_21_2 Q2.hinj88_21_2
      Q2.hcardT88_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_21_2 i) (Q2.hfix88_21_2 i) _)
      colCert_88_21_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T88_21
      hfix88_21 hinj88_21 hcardT88_21
      (fun i => conj_mem_of_fixedPoints _ _ (T88_21 i) (hfix88_21 i) _)
      ⟨88, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T88_21_2 Q2.hfix88_21_2 Q2.hinj88_21_2
      Q2.hcardT88_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_21_2 i) (Q2.hfix88_21_2 i) _)
      colCert_88_21_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T88_21
      hfix88_21 hinj88_21 hcardT88_21
      (fun i => conj_mem_of_fixedPoints _ _ (T88_21 i) (hfix88_21 i) _)
      ⟨88, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T88_21_2 Q2.hfix88_21_2 Q2.hinj88_21_2
      Q2.hcardT88_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_21_2 i) (Q2.hfix88_21_2 i) _)
      colCert_88_21_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T88_21
      hfix88_21 hinj88_21 hcardT88_21
      (fun i => conj_mem_of_fixedPoints _ _ (T88_21 i) (hfix88_21 i) _)
      ⟨88, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T88_21_2 Q2.hfix88_21_2 Q2.hinj88_21_2
      Q2.hcardT88_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_21_2 i) (Q2.hfix88_21_2 i) _)
      colCert_88_21_5.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T88_21
      hfix88_21 hinj88_21 hcardT88_21
      (fun i => conj_mem_of_fixedPoints _ _ (T88_21 i) (hfix88_21 i) _)
      ⟨88, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T88_21_2 Q2.hfix88_21_2 Q2.hinj88_21_2
      Q2.hcardT88_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_21_2 i) (Q2.hfix88_21_2 i) _)
      colCert_88_21_10.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T88_21
      hfix88_21 hinj88_21 hcardT88_21
      (fun i => conj_mem_of_fixedPoints _ _ (T88_21 i) (hfix88_21 i) _)
      ⟨88, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T88_21_2 Q2.hfix88_21_2 Q2.hinj88_21_2
      Q2.hcardT88_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_21_2 i) (Q2.hfix88_21_2 i) _)
      colCert_88_21_15.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T88_21
      hfix88_21 hinj88_21 hcardT88_21
      (fun i => conj_mem_of_fixedPoints _ _ (T88_21 i) (hfix88_21 i) _)
      ⟨88, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T88_21_2 Q2.hfix88_21_2 Q2.hinj88_21_2
      Q2.hcardT88_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_21_2 i) (Q2.hfix88_21_2 i) _)
      colCert_88_21_20.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T88_22
      hfix88_22 hinj88_22 hcardT88_22
      (fun i => conj_mem_of_fixedPoints _ _ (T88_22 i) (hfix88_22 i) _)
      ⟨88, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T88_22_2 Q2.hfix88_22_2 Q2.hinj88_22_2
      Q2.hcardT88_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_22_2 i) (Q2.hfix88_22_2 i) _)
      colCert_88_22_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T88_22
      hfix88_22 hinj88_22 hcardT88_22
      (fun i => conj_mem_of_fixedPoints _ _ (T88_22 i) (hfix88_22 i) _)
      ⟨88, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T88_22_2 Q2.hfix88_22_2 Q2.hinj88_22_2
      Q2.hcardT88_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_22_2 i) (Q2.hfix88_22_2 i) _)
      colCert_88_22_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T88_22
      hfix88_22 hinj88_22 hcardT88_22
      (fun i => conj_mem_of_fixedPoints _ _ (T88_22 i) (hfix88_22 i) _)
      ⟨88, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T88_22_2 Q2.hfix88_22_2 Q2.hinj88_22_2
      Q2.hcardT88_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_22_2 i) (Q2.hfix88_22_2 i) _)
      colCert_88_22_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T88_22
      hfix88_22 hinj88_22 hcardT88_22
      (fun i => conj_mem_of_fixedPoints _ _ (T88_22 i) (hfix88_22 i) _)
      ⟨88, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T88_22_2 Q2.hfix88_22_2 Q2.hinj88_22_2
      Q2.hcardT88_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_22_2 i) (Q2.hfix88_22_2 i) _)
      colCert_88_22_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T88_22
      hfix88_22 hinj88_22 hcardT88_22
      (fun i => conj_mem_of_fixedPoints _ _ (T88_22 i) (hfix88_22 i) _)
      ⟨88, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T88_22_2 Q2.hfix88_22_2 Q2.hinj88_22_2
      Q2.hcardT88_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_22_2 i) (Q2.hfix88_22_2 i) _)
      colCert_88_22_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T88_22
      hfix88_22 hinj88_22 hcardT88_22
      (fun i => conj_mem_of_fixedPoints _ _ (T88_22 i) (hfix88_22 i) _)
      ⟨88, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T88_22_2 Q2.hfix88_22_2 Q2.hinj88_22_2
      Q2.hcardT88_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_22_2 i) (Q2.hfix88_22_2 i) _)
      colCert_88_22_5.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T88_22
      hfix88_22 hinj88_22 hcardT88_22
      (fun i => conj_mem_of_fixedPoints _ _ (T88_22 i) (hfix88_22 i) _)
      ⟨88, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T88_22_2 Q2.hfix88_22_2 Q2.hinj88_22_2
      Q2.hcardT88_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_22_2 i) (Q2.hfix88_22_2 i) _)
      colCert_88_22_10.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T88_22
      hfix88_22 hinj88_22 hcardT88_22
      (fun i => conj_mem_of_fixedPoints _ _ (T88_22 i) (hfix88_22 i) _)
      ⟨88, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T88_22_2 Q2.hfix88_22_2 Q2.hinj88_22_2
      Q2.hcardT88_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_22_2 i) (Q2.hfix88_22_2 i) _)
      colCert_88_22_15.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T88_22
      hfix88_22 hinj88_22 hcardT88_22
      (fun i => conj_mem_of_fixedPoints _ _ (T88_22 i) (hfix88_22 i) _)
      ⟨88, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T88_22_2 Q2.hfix88_22_2 Q2.hinj88_22_2
      Q2.hcardT88_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_22_2 i) (Q2.hfix88_22_2 i) _)
      colCert_88_22_20.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T88_23
      hfix88_23 hinj88_23 hcardT88_23
      (fun i => conj_mem_of_fixedPoints _ _ (T88_23 i) (hfix88_23 i) _)
      ⟨88, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T88_23_2 Q2.hfix88_23_2 Q2.hinj88_23_2
      Q2.hcardT88_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_23_2 i) (Q2.hfix88_23_2 i) _)
      colCert_88_23_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T88_23
      hfix88_23 hinj88_23 hcardT88_23
      (fun i => conj_mem_of_fixedPoints _ _ (T88_23 i) (hfix88_23 i) _)
      ⟨88, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T88_23_2 Q2.hfix88_23_2 Q2.hinj88_23_2
      Q2.hcardT88_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_23_2 i) (Q2.hfix88_23_2 i) _)
      colCert_88_23_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T88_23
      hfix88_23 hinj88_23 hcardT88_23
      (fun i => conj_mem_of_fixedPoints _ _ (T88_23 i) (hfix88_23 i) _)
      ⟨88, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T88_23_2 Q2.hfix88_23_2 Q2.hinj88_23_2
      Q2.hcardT88_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_23_2 i) (Q2.hfix88_23_2 i) _)
      colCert_88_23_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T88_23
      hfix88_23 hinj88_23 hcardT88_23
      (fun i => conj_mem_of_fixedPoints _ _ (T88_23 i) (hfix88_23 i) _)
      ⟨88, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T88_23_2 Q2.hfix88_23_2 Q2.hinj88_23_2
      Q2.hcardT88_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_23_2 i) (Q2.hfix88_23_2 i) _)
      colCert_88_23_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T88_23
      hfix88_23 hinj88_23 hcardT88_23
      (fun i => conj_mem_of_fixedPoints _ _ (T88_23 i) (hfix88_23 i) _)
      ⟨88, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T88_23_2 Q2.hfix88_23_2 Q2.hinj88_23_2
      Q2.hcardT88_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_23_2 i) (Q2.hfix88_23_2 i) _)
      colCert_88_23_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T88_23
      hfix88_23 hinj88_23 hcardT88_23
      (fun i => conj_mem_of_fixedPoints _ _ (T88_23 i) (hfix88_23 i) _)
      ⟨88, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T88_23_2 Q2.hfix88_23_2 Q2.hinj88_23_2
      Q2.hcardT88_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_23_2 i) (Q2.hfix88_23_2 i) _)
      colCert_88_23_5.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T88_23
      hfix88_23 hinj88_23 hcardT88_23
      (fun i => conj_mem_of_fixedPoints _ _ (T88_23 i) (hfix88_23 i) _)
      ⟨88, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T88_23_2 Q2.hfix88_23_2 Q2.hinj88_23_2
      Q2.hcardT88_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_23_2 i) (Q2.hfix88_23_2 i) _)
      colCert_88_23_10.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T88_23
      hfix88_23 hinj88_23 hcardT88_23
      (fun i => conj_mem_of_fixedPoints _ _ (T88_23 i) (hfix88_23 i) _)
      ⟨88, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T88_23_2 Q2.hfix88_23_2 Q2.hinj88_23_2
      Q2.hcardT88_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_23_2 i) (Q2.hfix88_23_2 i) _)
      colCert_88_23_15.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T88_23
      hfix88_23 hinj88_23 hcardT88_23
      (fun i => conj_mem_of_fixedPoints _ _ (T88_23 i) (hfix88_23 i) _)
      ⟨88, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T88_23_2 Q2.hfix88_23_2 Q2.hinj88_23_2
      Q2.hcardT88_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_23_2 i) (Q2.hfix88_23_2 i) _)
      colCert_88_23_20.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T88_24
      hfix88_24 hinj88_24 hcardT88_24
      (fun i => conj_mem_of_fixedPoints _ _ (T88_24 i) (hfix88_24 i) _)
      ⟨88, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T88_24_2 Q2.hfix88_24_2 Q2.hinj88_24_2
      Q2.hcardT88_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_24_2 i) (Q2.hfix88_24_2 i) _)
      colCert_88_24_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T88_24
      hfix88_24 hinj88_24 hcardT88_24
      (fun i => conj_mem_of_fixedPoints _ _ (T88_24 i) (hfix88_24 i) _)
      ⟨88, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T88_24_2 Q2.hfix88_24_2 Q2.hinj88_24_2
      Q2.hcardT88_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_24_2 i) (Q2.hfix88_24_2 i) _)
      colCert_88_24_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T88_24
      hfix88_24 hinj88_24 hcardT88_24
      (fun i => conj_mem_of_fixedPoints _ _ (T88_24 i) (hfix88_24 i) _)
      ⟨88, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T88_24_2 Q2.hfix88_24_2 Q2.hinj88_24_2
      Q2.hcardT88_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_24_2 i) (Q2.hfix88_24_2 i) _)
      colCert_88_24_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T88_24
      hfix88_24 hinj88_24 hcardT88_24
      (fun i => conj_mem_of_fixedPoints _ _ (T88_24 i) (hfix88_24 i) _)
      ⟨88, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T88_24_2 Q2.hfix88_24_2 Q2.hinj88_24_2
      Q2.hcardT88_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_24_2 i) (Q2.hfix88_24_2 i) _)
      colCert_88_24_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T88_24
      hfix88_24 hinj88_24 hcardT88_24
      (fun i => conj_mem_of_fixedPoints _ _ (T88_24 i) (hfix88_24 i) _)
      ⟨88, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T88_24_2 Q2.hfix88_24_2 Q2.hinj88_24_2
      Q2.hcardT88_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_24_2 i) (Q2.hfix88_24_2 i) _)
      colCert_88_24_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T88_24
      hfix88_24 hinj88_24 hcardT88_24
      (fun i => conj_mem_of_fixedPoints _ _ (T88_24 i) (hfix88_24 i) _)
      ⟨88, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T88_24_2 Q2.hfix88_24_2 Q2.hinj88_24_2
      Q2.hcardT88_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_24_2 i) (Q2.hfix88_24_2 i) _)
      colCert_88_24_5.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T88_24
      hfix88_24 hinj88_24 hcardT88_24
      (fun i => conj_mem_of_fixedPoints _ _ (T88_24 i) (hfix88_24 i) _)
      ⟨88, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T88_24_2 Q2.hfix88_24_2 Q2.hinj88_24_2
      Q2.hcardT88_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_24_2 i) (Q2.hfix88_24_2 i) _)
      colCert_88_24_10.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T88_24
      hfix88_24 hinj88_24 hcardT88_24
      (fun i => conj_mem_of_fixedPoints _ _ (T88_24 i) (hfix88_24 i) _)
      ⟨88, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T88_24_2 Q2.hfix88_24_2 Q2.hinj88_24_2
      Q2.hcardT88_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_24_2 i) (Q2.hfix88_24_2 i) _)
      colCert_88_24_15.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T88_24
      hfix88_24 hinj88_24 hcardT88_24
      (fun i => conj_mem_of_fixedPoints _ _ (T88_24 i) (hfix88_24 i) _)
      ⟨88, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T88_24_2 Q2.hfix88_24_2 Q2.hinj88_24_2
      Q2.hcardT88_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_24_2 i) (Q2.hfix88_24_2 i) _)
      colCert_88_24_20.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T88_54
      hfix88_54 hinj88_54 hcardT88_54
      (fun i => conj_mem_of_fixedPoints _ _ (T88_54 i) (hfix88_54 i) _)
      ⟨88, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T88_54_2 Q2.hfix88_54_2 Q2.hinj88_54_2
      Q2.hcardT88_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_54_2 i) (Q2.hfix88_54_2 i) _)
      colCert_88_54_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T88_54
      hfix88_54 hinj88_54 hcardT88_54
      (fun i => conj_mem_of_fixedPoints _ _ (T88_54 i) (hfix88_54 i) _)
      ⟨88, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T88_54_2 Q2.hfix88_54_2 Q2.hinj88_54_2
      Q2.hcardT88_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_54_2 i) (Q2.hfix88_54_2 i) _)
      colCert_88_54_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T88_54
      hfix88_54 hinj88_54 hcardT88_54
      (fun i => conj_mem_of_fixedPoints _ _ (T88_54 i) (hfix88_54 i) _)
      ⟨88, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T88_54_2 Q2.hfix88_54_2 Q2.hinj88_54_2
      Q2.hcardT88_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_54_2 i) (Q2.hfix88_54_2 i) _)
      colCert_88_54_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T88_54
      hfix88_54 hinj88_54 hcardT88_54
      (fun i => conj_mem_of_fixedPoints _ _ (T88_54 i) (hfix88_54 i) _)
      ⟨88, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T88_54_2 Q2.hfix88_54_2 Q2.hinj88_54_2
      Q2.hcardT88_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_54_2 i) (Q2.hfix88_54_2 i) _)
      colCert_88_54_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T88_54
      hfix88_54 hinj88_54 hcardT88_54
      (fun i => conj_mem_of_fixedPoints _ _ (T88_54 i) (hfix88_54 i) _)
      ⟨88, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T88_54_2 Q2.hfix88_54_2 Q2.hinj88_54_2
      Q2.hcardT88_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_54_2 i) (Q2.hfix88_54_2 i) _)
      colCert_88_54_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T88_54
      hfix88_54 hinj88_54 hcardT88_54
      (fun i => conj_mem_of_fixedPoints _ _ (T88_54 i) (hfix88_54 i) _)
      ⟨88, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T88_54_2 Q2.hfix88_54_2 Q2.hinj88_54_2
      Q2.hcardT88_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_54_2 i) (Q2.hfix88_54_2 i) _)
      colCert_88_54_5.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T88_54
      hfix88_54 hinj88_54 hcardT88_54
      (fun i => conj_mem_of_fixedPoints _ _ (T88_54 i) (hfix88_54 i) _)
      ⟨88, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T88_54_2 Q2.hfix88_54_2 Q2.hinj88_54_2
      Q2.hcardT88_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_54_2 i) (Q2.hfix88_54_2 i) _)
      colCert_88_54_10.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T88_54
      hfix88_54 hinj88_54 hcardT88_54
      (fun i => conj_mem_of_fixedPoints _ _ (T88_54 i) (hfix88_54 i) _)
      ⟨88, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T88_54_2 Q2.hfix88_54_2 Q2.hinj88_54_2
      Q2.hcardT88_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_54_2 i) (Q2.hfix88_54_2 i) _)
      colCert_88_54_15.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T88_54
      hfix88_54 hinj88_54 hcardT88_54
      (fun i => conj_mem_of_fixedPoints _ _ (T88_54 i) (hfix88_54 i) _)
      ⟨88, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T88_54_2 Q2.hfix88_54_2 Q2.hinj88_54_2
      Q2.hcardT88_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_54_2 i) (Q2.hfix88_54_2 i) _)
      colCert_88_54_20.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_0 (hp : 0 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 0 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 0 (transLenTr ⟨88, by decide⟩ 0 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 0 (transLenTr ⟨88, by decide⟩ 0 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 0 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_0.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_1 (hp : 1 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 1 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 1 (transLenTr ⟨88, by decide⟩ 1 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 1 (transLenTr ⟨88, by decide⟩ 1 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 1 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_1.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_2 (hp : 2 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 2 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 2 (transLenTr ⟨88, by decide⟩ 2 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 2 (transLenTr ⟨88, by decide⟩ 2 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 2 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_2.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_3 (hp : 3 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 3 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 3 (transLenTr ⟨88, by decide⟩ 3 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 3 (transLenTr ⟨88, by decide⟩ 3 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 3 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_3.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_4 (hp : 4 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 4 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 4 (transLenTr ⟨88, by decide⟩ 4 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 4 (transLenTr ⟨88, by decide⟩ 4 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 4 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_4.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_5 (hp : 5 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 5 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 5 (transLenTr ⟨88, by decide⟩ 5 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 5 (transLenTr ⟨88, by decide⟩ 5 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 5 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_5.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_6 (hp : 6 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 6 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 6 (transLenTr ⟨88, by decide⟩ 6 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 6 (transLenTr ⟨88, by decide⟩ 6 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 6 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_6.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_7 (hp : 7 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 7 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 7 (transLenTr ⟨88, by decide⟩ 7 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 7 (transLenTr ⟨88, by decide⟩ 7 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 7 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_7.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_8 (hp : 8 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 8 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 8 (transLenTr ⟨88, by decide⟩ 8 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 8 (transLenTr ⟨88, by decide⟩ 8 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 8 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_8.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_9 (hp : 9 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 9 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 9 (transLenTr ⟨88, by decide⟩ 9 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 9 (transLenTr ⟨88, by decide⟩ 9 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 9 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_9.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_10 (hp : 10 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 10 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 10 (transLenTr ⟨88, by decide⟩ 10 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 10 (transLenTr ⟨88, by decide⟩ 10 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 10 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_10.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_11 (hp : 11 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 11 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 11 (transLenTr ⟨88, by decide⟩ 11 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 11 (transLenTr ⟨88, by decide⟩ 11 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 11 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_11.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_12 (hp : 12 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 12 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 12 (transLenTr ⟨88, by decide⟩ 12 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 12 (transLenTr ⟨88, by decide⟩ 12 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 12 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_12.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_13 (hp : 13 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 13 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 13 (transLenTr ⟨88, by decide⟩ 13 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 13 (transLenTr ⟨88, by decide⟩ 13 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 13 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_13.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_14 (hp : 14 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 14 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 14 (transLenTr ⟨88, by decide⟩ 14 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 14 (transLenTr ⟨88, by decide⟩ 14 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 14 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_14.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_15 (hp : 15 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 15 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 15 (transLenTr ⟨88, by decide⟩ 15 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 15 (transLenTr ⟨88, by decide⟩ 15 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 15 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_15.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_16 (hp : 16 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 16 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 16 (transLenTr ⟨88, by decide⟩ 16 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 16 (transLenTr ⟨88, by decide⟩ 16 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 16 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_16.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_17 (hp : 17 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 17 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 17 (transLenTr ⟨88, by decide⟩ 17 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 17 (transLenTr ⟨88, by decide⟩ 17 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 17 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_17.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_18 (hp : 18 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 18 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 18 (transLenTr ⟨88, by decide⟩ 18 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 18 (transLenTr ⟨88, by decide⟩ 18 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 18 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_18.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_19 (hp : 19 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 19 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 19 (transLenTr ⟨88, by decide⟩ 19 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 19 (transLenTr ⟨88, by decide⟩ 19 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 19 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_19.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_20 (hp : 20 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 20 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 20 (transLenTr ⟨88, by decide⟩ 20 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 20 (transLenTr ⟨88, by decide⟩ 20 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 20 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_20.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_21 (hp : 21 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 21 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 21 (transLenTr ⟨88, by decide⟩ 21 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 21 (transLenTr ⟨88, by decide⟩ 21 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 21 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_21.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_22 (hp : 22 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 22 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 22 (transLenTr ⟨88, by decide⟩ 22 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 22 (transLenTr ⟨88, by decide⟩ 22 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 22 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_22.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_23 (hp : 23 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 23 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 23 (transLenTr ⟨88, by decide⟩ 23 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 23 (transLenTr ⟨88, by decide⟩ 23 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 23 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_23.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_88_88_24 (hp : 24 < (Q2.transData.getD 88 []).length)
    (j : Nat) (hj : j < (repChars.getD 88 []).length)
    (hq : (normIsRep.getD 88 []).getD j false = true) :
    species (Q2.reps (⟨88, by decide⟩ : Fin 148)) (colE2 ⟨88, by decide⟩ 24 hp)
        (rowE2 (⟨88, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨88, by decide⟩ : Fin 148))
        (colE1 ⟨88, by decide⟩ 24 (transLenTr ⟨88, by decide⟩ 24 hp))
        (rowE1 (⟨88, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨88, by decide⟩ : Fin 148) ⟨88, by decide⟩ _
      (validAt ⟨88, by decide⟩ (listedAt ⟨88, by decide⟩ hj))
      (colE1 ⟨88, by decide⟩ 24 (transLenTr ⟨88, by decide⟩ 24 hp)) T88_88
      hfix88_88 hinj88_88 hcardT88_88
      (fun i => conj_mem_of_fixedPoints _ _ (T88_88 i) (hfix88_88 i) _)
      ⟨88, by decide⟩ ⟨88, by decide⟩ _
      (Q2.validAt ⟨88, by decide⟩ (Q2.listedAt ⟨88, by decide⟩
        (alnCheck_rep ⟨88, by decide⟩ hj hq).1))
      (colE2 ⟨88, by decide⟩ 24 hp) Q2.T88_88_2 Q2.hfix88_88_2 Q2.hinj88_88_2
      Q2.hcardT88_88_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T88_88_2 i) (Q2.hfix88_88_2 i) _)
      colCert_88_88_24.hD ?_).symm
  rw [alnId_88 j hj]


theorem leaf_89_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T89_2
      hfix89_2 hinj89_2 hcardT89_2
      (fun i => conj_mem_of_fixedPoints _ _ (T89_2 i) (hfix89_2 i) _)
      ⟨89, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T89_2_2 Q2.hfix89_2_2 Q2.hinj89_2_2
      Q2.hcardT89_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_2_2 i) (Q2.hfix89_2_2 i) _)
      colCert_89_2_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T89_2
      hfix89_2 hinj89_2 hcardT89_2
      (fun i => conj_mem_of_fixedPoints _ _ (T89_2 i) (hfix89_2 i) _)
      ⟨89, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T89_2_2 Q2.hfix89_2_2 Q2.hinj89_2_2
      Q2.hcardT89_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_2_2 i) (Q2.hfix89_2_2 i) _)
      colCert_89_2_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T89_2
      hfix89_2 hinj89_2 hcardT89_2
      (fun i => conj_mem_of_fixedPoints _ _ (T89_2 i) (hfix89_2 i) _)
      ⟨89, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T89_2_2 Q2.hfix89_2_2 Q2.hinj89_2_2
      Q2.hcardT89_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_2_2 i) (Q2.hfix89_2_2 i) _)
      colCert_89_2_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T89_2
      hfix89_2 hinj89_2 hcardT89_2
      (fun i => conj_mem_of_fixedPoints _ _ (T89_2 i) (hfix89_2 i) _)
      ⟨89, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T89_2_2 Q2.hfix89_2_2 Q2.hinj89_2_2
      Q2.hcardT89_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_2_2 i) (Q2.hfix89_2_2 i) _)
      colCert_89_2_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T89_2
      hfix89_2 hinj89_2 hcardT89_2
      (fun i => conj_mem_of_fixedPoints _ _ (T89_2 i) (hfix89_2 i) _)
      ⟨89, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T89_2_2 Q2.hfix89_2_2 Q2.hinj89_2_2
      Q2.hcardT89_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_2_2 i) (Q2.hfix89_2_2 i) _)
      colCert_89_2_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T89_3
      hfix89_3 hinj89_3 hcardT89_3
      (fun i => conj_mem_of_fixedPoints _ _ (T89_3 i) (hfix89_3 i) _)
      ⟨89, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T89_3_2 Q2.hfix89_3_2 Q2.hinj89_3_2
      Q2.hcardT89_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_3_2 i) (Q2.hfix89_3_2 i) _)
      colCert_89_3_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T89_3
      hfix89_3 hinj89_3 hcardT89_3
      (fun i => conj_mem_of_fixedPoints _ _ (T89_3 i) (hfix89_3 i) _)
      ⟨89, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T89_3_2 Q2.hfix89_3_2 Q2.hinj89_3_2
      Q2.hcardT89_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_3_2 i) (Q2.hfix89_3_2 i) _)
      colCert_89_3_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T89_3
      hfix89_3 hinj89_3 hcardT89_3
      (fun i => conj_mem_of_fixedPoints _ _ (T89_3 i) (hfix89_3 i) _)
      ⟨89, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T89_3_2 Q2.hfix89_3_2 Q2.hinj89_3_2
      Q2.hcardT89_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_3_2 i) (Q2.hfix89_3_2 i) _)
      colCert_89_3_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T89_3
      hfix89_3 hinj89_3 hcardT89_3
      (fun i => conj_mem_of_fixedPoints _ _ (T89_3 i) (hfix89_3 i) _)
      ⟨89, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T89_3_2 Q2.hfix89_3_2 Q2.hinj89_3_2
      Q2.hcardT89_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_3_2 i) (Q2.hfix89_3_2 i) _)
      colCert_89_3_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T89_3
      hfix89_3 hinj89_3 hcardT89_3
      (fun i => conj_mem_of_fixedPoints _ _ (T89_3 i) (hfix89_3 i) _)
      ⟨89, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T89_3_2 Q2.hfix89_3_2 Q2.hinj89_3_2
      Q2.hcardT89_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_3_2 i) (Q2.hfix89_3_2 i) _)
      colCert_89_3_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T89_4
      hfix89_4 hinj89_4 hcardT89_4
      (fun i => conj_mem_of_fixedPoints _ _ (T89_4 i) (hfix89_4 i) _)
      ⟨89, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T89_4_2 Q2.hfix89_4_2 Q2.hinj89_4_2
      Q2.hcardT89_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_4_2 i) (Q2.hfix89_4_2 i) _)
      colCert_89_4_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T89_4
      hfix89_4 hinj89_4 hcardT89_4
      (fun i => conj_mem_of_fixedPoints _ _ (T89_4 i) (hfix89_4 i) _)
      ⟨89, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T89_4_2 Q2.hfix89_4_2 Q2.hinj89_4_2
      Q2.hcardT89_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_4_2 i) (Q2.hfix89_4_2 i) _)
      colCert_89_4_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T89_4
      hfix89_4 hinj89_4 hcardT89_4
      (fun i => conj_mem_of_fixedPoints _ _ (T89_4 i) (hfix89_4 i) _)
      ⟨89, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T89_4_2 Q2.hfix89_4_2 Q2.hinj89_4_2
      Q2.hcardT89_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_4_2 i) (Q2.hfix89_4_2 i) _)
      colCert_89_4_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T89_4
      hfix89_4 hinj89_4 hcardT89_4
      (fun i => conj_mem_of_fixedPoints _ _ (T89_4 i) (hfix89_4 i) _)
      ⟨89, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T89_4_2 Q2.hfix89_4_2 Q2.hinj89_4_2
      Q2.hcardT89_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_4_2 i) (Q2.hfix89_4_2 i) _)
      colCert_89_4_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T89_4
      hfix89_4 hinj89_4 hcardT89_4
      (fun i => conj_mem_of_fixedPoints _ _ (T89_4 i) (hfix89_4 i) _)
      ⟨89, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T89_4_2 Q2.hfix89_4_2 Q2.hinj89_4_2
      Q2.hcardT89_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_4_2 i) (Q2.hfix89_4_2 i) _)
      colCert_89_4_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T89_5
      hfix89_5 hinj89_5 hcardT89_5
      (fun i => conj_mem_of_fixedPoints _ _ (T89_5 i) (hfix89_5 i) _)
      ⟨89, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T89_5_2 Q2.hfix89_5_2 Q2.hinj89_5_2
      Q2.hcardT89_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_5_2 i) (Q2.hfix89_5_2 i) _)
      colCert_89_5_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T89_5
      hfix89_5 hinj89_5 hcardT89_5
      (fun i => conj_mem_of_fixedPoints _ _ (T89_5 i) (hfix89_5 i) _)
      ⟨89, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T89_5_2 Q2.hfix89_5_2 Q2.hinj89_5_2
      Q2.hcardT89_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_5_2 i) (Q2.hfix89_5_2 i) _)
      colCert_89_5_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T89_5
      hfix89_5 hinj89_5 hcardT89_5
      (fun i => conj_mem_of_fixedPoints _ _ (T89_5 i) (hfix89_5 i) _)
      ⟨89, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T89_5_2 Q2.hfix89_5_2 Q2.hinj89_5_2
      Q2.hcardT89_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_5_2 i) (Q2.hfix89_5_2 i) _)
      colCert_89_5_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T89_5
      hfix89_5 hinj89_5 hcardT89_5
      (fun i => conj_mem_of_fixedPoints _ _ (T89_5 i) (hfix89_5 i) _)
      ⟨89, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T89_5_2 Q2.hfix89_5_2 Q2.hinj89_5_2
      Q2.hcardT89_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_5_2 i) (Q2.hfix89_5_2 i) _)
      colCert_89_5_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T89_5
      hfix89_5 hinj89_5 hcardT89_5
      (fun i => conj_mem_of_fixedPoints _ _ (T89_5 i) (hfix89_5 i) _)
      ⟨89, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T89_5_2 Q2.hfix89_5_2 Q2.hinj89_5_2
      Q2.hcardT89_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_5_2 i) (Q2.hfix89_5_2 i) _)
      colCert_89_5_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T89_8
      hfix89_8 hinj89_8 hcardT89_8
      (fun i => conj_mem_of_fixedPoints _ _ (T89_8 i) (hfix89_8 i) _)
      ⟨89, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T89_8_2 Q2.hfix89_8_2 Q2.hinj89_8_2
      Q2.hcardT89_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_8_2 i) (Q2.hfix89_8_2 i) _)
      colCert_89_8_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T89_8
      hfix89_8 hinj89_8 hcardT89_8
      (fun i => conj_mem_of_fixedPoints _ _ (T89_8 i) (hfix89_8 i) _)
      ⟨89, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T89_8_2 Q2.hfix89_8_2 Q2.hinj89_8_2
      Q2.hcardT89_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_8_2 i) (Q2.hfix89_8_2 i) _)
      colCert_89_8_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T89_8
      hfix89_8 hinj89_8 hcardT89_8
      (fun i => conj_mem_of_fixedPoints _ _ (T89_8 i) (hfix89_8 i) _)
      ⟨89, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T89_8_2 Q2.hfix89_8_2 Q2.hinj89_8_2
      Q2.hcardT89_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_8_2 i) (Q2.hfix89_8_2 i) _)
      colCert_89_8_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T89_8
      hfix89_8 hinj89_8 hcardT89_8
      (fun i => conj_mem_of_fixedPoints _ _ (T89_8 i) (hfix89_8 i) _)
      ⟨89, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T89_8_2 Q2.hfix89_8_2 Q2.hinj89_8_2
      Q2.hcardT89_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_8_2 i) (Q2.hfix89_8_2 i) _)
      colCert_89_8_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T89_8
      hfix89_8 hinj89_8 hcardT89_8
      (fun i => conj_mem_of_fixedPoints _ _ (T89_8 i) (hfix89_8 i) _)
      ⟨89, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T89_8_2 Q2.hfix89_8_2 Q2.hinj89_8_2
      Q2.hcardT89_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_8_2 i) (Q2.hfix89_8_2 i) _)
      colCert_89_8_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T89_11
      hfix89_11 hinj89_11 hcardT89_11
      (fun i => conj_mem_of_fixedPoints _ _ (T89_11 i) (hfix89_11 i) _)
      ⟨89, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T89_11_2 Q2.hfix89_11_2 Q2.hinj89_11_2
      Q2.hcardT89_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_11_2 i) (Q2.hfix89_11_2 i) _)
      colCert_89_11_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T89_11
      hfix89_11 hinj89_11 hcardT89_11
      (fun i => conj_mem_of_fixedPoints _ _ (T89_11 i) (hfix89_11 i) _)
      ⟨89, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T89_11_2 Q2.hfix89_11_2 Q2.hinj89_11_2
      Q2.hcardT89_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_11_2 i) (Q2.hfix89_11_2 i) _)
      colCert_89_11_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T89_11
      hfix89_11 hinj89_11 hcardT89_11
      (fun i => conj_mem_of_fixedPoints _ _ (T89_11 i) (hfix89_11 i) _)
      ⟨89, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T89_11_2 Q2.hfix89_11_2 Q2.hinj89_11_2
      Q2.hcardT89_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_11_2 i) (Q2.hfix89_11_2 i) _)
      colCert_89_11_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T89_11
      hfix89_11 hinj89_11 hcardT89_11
      (fun i => conj_mem_of_fixedPoints _ _ (T89_11 i) (hfix89_11 i) _)
      ⟨89, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T89_11_2 Q2.hfix89_11_2 Q2.hinj89_11_2
      Q2.hcardT89_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_11_2 i) (Q2.hfix89_11_2 i) _)
      colCert_89_11_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T89_11
      hfix89_11 hinj89_11 hcardT89_11
      (fun i => conj_mem_of_fixedPoints _ _ (T89_11 i) (hfix89_11 i) _)
      ⟨89, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T89_11_2 Q2.hfix89_11_2 Q2.hinj89_11_2
      Q2.hcardT89_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_11_2 i) (Q2.hfix89_11_2 i) _)
      colCert_89_11_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T89_12
      hfix89_12 hinj89_12 hcardT89_12
      (fun i => conj_mem_of_fixedPoints _ _ (T89_12 i) (hfix89_12 i) _)
      ⟨89, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T89_12_2 Q2.hfix89_12_2 Q2.hinj89_12_2
      Q2.hcardT89_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_12_2 i) (Q2.hfix89_12_2 i) _)
      colCert_89_12_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T89_12
      hfix89_12 hinj89_12 hcardT89_12
      (fun i => conj_mem_of_fixedPoints _ _ (T89_12 i) (hfix89_12 i) _)
      ⟨89, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T89_12_2 Q2.hfix89_12_2 Q2.hinj89_12_2
      Q2.hcardT89_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_12_2 i) (Q2.hfix89_12_2 i) _)
      colCert_89_12_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T89_12
      hfix89_12 hinj89_12 hcardT89_12
      (fun i => conj_mem_of_fixedPoints _ _ (T89_12 i) (hfix89_12 i) _)
      ⟨89, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T89_12_2 Q2.hfix89_12_2 Q2.hinj89_12_2
      Q2.hcardT89_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_12_2 i) (Q2.hfix89_12_2 i) _)
      colCert_89_12_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T89_12
      hfix89_12 hinj89_12 hcardT89_12
      (fun i => conj_mem_of_fixedPoints _ _ (T89_12 i) (hfix89_12 i) _)
      ⟨89, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T89_12_2 Q2.hfix89_12_2 Q2.hinj89_12_2
      Q2.hcardT89_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_12_2 i) (Q2.hfix89_12_2 i) _)
      colCert_89_12_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T89_12
      hfix89_12 hinj89_12 hcardT89_12
      (fun i => conj_mem_of_fixedPoints _ _ (T89_12 i) (hfix89_12 i) _)
      ⟨89, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T89_12_2 Q2.hfix89_12_2 Q2.hinj89_12_2
      Q2.hcardT89_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_12_2 i) (Q2.hfix89_12_2 i) _)
      colCert_89_12_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T89_20
      hfix89_20 hinj89_20 hcardT89_20
      (fun i => conj_mem_of_fixedPoints _ _ (T89_20 i) (hfix89_20 i) _)
      ⟨89, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T89_20_2 Q2.hfix89_20_2 Q2.hinj89_20_2
      Q2.hcardT89_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_20_2 i) (Q2.hfix89_20_2 i) _)
      colCert_89_20_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T89_20
      hfix89_20 hinj89_20 hcardT89_20
      (fun i => conj_mem_of_fixedPoints _ _ (T89_20 i) (hfix89_20 i) _)
      ⟨89, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T89_20_2 Q2.hfix89_20_2 Q2.hinj89_20_2
      Q2.hcardT89_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_20_2 i) (Q2.hfix89_20_2 i) _)
      colCert_89_20_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T89_20
      hfix89_20 hinj89_20 hcardT89_20
      (fun i => conj_mem_of_fixedPoints _ _ (T89_20 i) (hfix89_20 i) _)
      ⟨89, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T89_20_2 Q2.hfix89_20_2 Q2.hinj89_20_2
      Q2.hcardT89_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_20_2 i) (Q2.hfix89_20_2 i) _)
      colCert_89_20_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T89_20
      hfix89_20 hinj89_20 hcardT89_20
      (fun i => conj_mem_of_fixedPoints _ _ (T89_20 i) (hfix89_20 i) _)
      ⟨89, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T89_20_2 Q2.hfix89_20_2 Q2.hinj89_20_2
      Q2.hcardT89_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_20_2 i) (Q2.hfix89_20_2 i) _)
      colCert_89_20_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T89_20
      hfix89_20 hinj89_20 hcardT89_20
      (fun i => conj_mem_of_fixedPoints _ _ (T89_20 i) (hfix89_20 i) _)
      ⟨89, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T89_20_2 Q2.hfix89_20_2 Q2.hinj89_20_2
      Q2.hcardT89_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_20_2 i) (Q2.hfix89_20_2 i) _)
      colCert_89_20_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T89_20
      hfix89_20 hinj89_20 hcardT89_20
      (fun i => conj_mem_of_fixedPoints _ _ (T89_20 i) (hfix89_20 i) _)
      ⟨89, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T89_20_2 Q2.hfix89_20_2 Q2.hinj89_20_2
      Q2.hcardT89_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_20_2 i) (Q2.hfix89_20_2 i) _)
      colCert_89_20_5.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T89_20
      hfix89_20 hinj89_20 hcardT89_20
      (fun i => conj_mem_of_fixedPoints _ _ (T89_20 i) (hfix89_20 i) _)
      ⟨89, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T89_20_2 Q2.hfix89_20_2 Q2.hinj89_20_2
      Q2.hcardT89_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_20_2 i) (Q2.hfix89_20_2 i) _)
      colCert_89_20_10.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T89_20
      hfix89_20 hinj89_20 hcardT89_20
      (fun i => conj_mem_of_fixedPoints _ _ (T89_20 i) (hfix89_20 i) _)
      ⟨89, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T89_20_2 Q2.hfix89_20_2 Q2.hinj89_20_2
      Q2.hcardT89_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_20_2 i) (Q2.hfix89_20_2 i) _)
      colCert_89_20_15.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T89_20
      hfix89_20 hinj89_20 hcardT89_20
      (fun i => conj_mem_of_fixedPoints _ _ (T89_20 i) (hfix89_20 i) _)
      ⟨89, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T89_20_2 Q2.hfix89_20_2 Q2.hinj89_20_2
      Q2.hcardT89_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_20_2 i) (Q2.hfix89_20_2 i) _)
      colCert_89_20_20.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T89_21
      hfix89_21 hinj89_21 hcardT89_21
      (fun i => conj_mem_of_fixedPoints _ _ (T89_21 i) (hfix89_21 i) _)
      ⟨89, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T89_21_2 Q2.hfix89_21_2 Q2.hinj89_21_2
      Q2.hcardT89_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_21_2 i) (Q2.hfix89_21_2 i) _)
      colCert_89_21_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T89_21
      hfix89_21 hinj89_21 hcardT89_21
      (fun i => conj_mem_of_fixedPoints _ _ (T89_21 i) (hfix89_21 i) _)
      ⟨89, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T89_21_2 Q2.hfix89_21_2 Q2.hinj89_21_2
      Q2.hcardT89_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_21_2 i) (Q2.hfix89_21_2 i) _)
      colCert_89_21_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T89_21
      hfix89_21 hinj89_21 hcardT89_21
      (fun i => conj_mem_of_fixedPoints _ _ (T89_21 i) (hfix89_21 i) _)
      ⟨89, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T89_21_2 Q2.hfix89_21_2 Q2.hinj89_21_2
      Q2.hcardT89_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_21_2 i) (Q2.hfix89_21_2 i) _)
      colCert_89_21_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T89_21
      hfix89_21 hinj89_21 hcardT89_21
      (fun i => conj_mem_of_fixedPoints _ _ (T89_21 i) (hfix89_21 i) _)
      ⟨89, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T89_21_2 Q2.hfix89_21_2 Q2.hinj89_21_2
      Q2.hcardT89_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_21_2 i) (Q2.hfix89_21_2 i) _)
      colCert_89_21_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T89_21
      hfix89_21 hinj89_21 hcardT89_21
      (fun i => conj_mem_of_fixedPoints _ _ (T89_21 i) (hfix89_21 i) _)
      ⟨89, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T89_21_2 Q2.hfix89_21_2 Q2.hinj89_21_2
      Q2.hcardT89_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_21_2 i) (Q2.hfix89_21_2 i) _)
      colCert_89_21_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T89_21
      hfix89_21 hinj89_21 hcardT89_21
      (fun i => conj_mem_of_fixedPoints _ _ (T89_21 i) (hfix89_21 i) _)
      ⟨89, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T89_21_2 Q2.hfix89_21_2 Q2.hinj89_21_2
      Q2.hcardT89_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_21_2 i) (Q2.hfix89_21_2 i) _)
      colCert_89_21_5.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T89_21
      hfix89_21 hinj89_21 hcardT89_21
      (fun i => conj_mem_of_fixedPoints _ _ (T89_21 i) (hfix89_21 i) _)
      ⟨89, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T89_21_2 Q2.hfix89_21_2 Q2.hinj89_21_2
      Q2.hcardT89_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_21_2 i) (Q2.hfix89_21_2 i) _)
      colCert_89_21_10.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T89_21
      hfix89_21 hinj89_21 hcardT89_21
      (fun i => conj_mem_of_fixedPoints _ _ (T89_21 i) (hfix89_21 i) _)
      ⟨89, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T89_21_2 Q2.hfix89_21_2 Q2.hinj89_21_2
      Q2.hcardT89_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_21_2 i) (Q2.hfix89_21_2 i) _)
      colCert_89_21_15.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T89_21
      hfix89_21 hinj89_21 hcardT89_21
      (fun i => conj_mem_of_fixedPoints _ _ (T89_21 i) (hfix89_21 i) _)
      ⟨89, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T89_21_2 Q2.hfix89_21_2 Q2.hinj89_21_2
      Q2.hcardT89_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_21_2 i) (Q2.hfix89_21_2 i) _)
      colCert_89_21_20.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T89_22
      hfix89_22 hinj89_22 hcardT89_22
      (fun i => conj_mem_of_fixedPoints _ _ (T89_22 i) (hfix89_22 i) _)
      ⟨89, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T89_22_2 Q2.hfix89_22_2 Q2.hinj89_22_2
      Q2.hcardT89_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_22_2 i) (Q2.hfix89_22_2 i) _)
      colCert_89_22_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T89_22
      hfix89_22 hinj89_22 hcardT89_22
      (fun i => conj_mem_of_fixedPoints _ _ (T89_22 i) (hfix89_22 i) _)
      ⟨89, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T89_22_2 Q2.hfix89_22_2 Q2.hinj89_22_2
      Q2.hcardT89_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_22_2 i) (Q2.hfix89_22_2 i) _)
      colCert_89_22_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T89_22
      hfix89_22 hinj89_22 hcardT89_22
      (fun i => conj_mem_of_fixedPoints _ _ (T89_22 i) (hfix89_22 i) _)
      ⟨89, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T89_22_2 Q2.hfix89_22_2 Q2.hinj89_22_2
      Q2.hcardT89_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_22_2 i) (Q2.hfix89_22_2 i) _)
      colCert_89_22_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T89_22
      hfix89_22 hinj89_22 hcardT89_22
      (fun i => conj_mem_of_fixedPoints _ _ (T89_22 i) (hfix89_22 i) _)
      ⟨89, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T89_22_2 Q2.hfix89_22_2 Q2.hinj89_22_2
      Q2.hcardT89_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_22_2 i) (Q2.hfix89_22_2 i) _)
      colCert_89_22_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T89_22
      hfix89_22 hinj89_22 hcardT89_22
      (fun i => conj_mem_of_fixedPoints _ _ (T89_22 i) (hfix89_22 i) _)
      ⟨89, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T89_22_2 Q2.hfix89_22_2 Q2.hinj89_22_2
      Q2.hcardT89_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_22_2 i) (Q2.hfix89_22_2 i) _)
      colCert_89_22_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T89_22
      hfix89_22 hinj89_22 hcardT89_22
      (fun i => conj_mem_of_fixedPoints _ _ (T89_22 i) (hfix89_22 i) _)
      ⟨89, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T89_22_2 Q2.hfix89_22_2 Q2.hinj89_22_2
      Q2.hcardT89_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_22_2 i) (Q2.hfix89_22_2 i) _)
      colCert_89_22_5.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T89_22
      hfix89_22 hinj89_22 hcardT89_22
      (fun i => conj_mem_of_fixedPoints _ _ (T89_22 i) (hfix89_22 i) _)
      ⟨89, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T89_22_2 Q2.hfix89_22_2 Q2.hinj89_22_2
      Q2.hcardT89_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_22_2 i) (Q2.hfix89_22_2 i) _)
      colCert_89_22_10.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T89_22
      hfix89_22 hinj89_22 hcardT89_22
      (fun i => conj_mem_of_fixedPoints _ _ (T89_22 i) (hfix89_22 i) _)
      ⟨89, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T89_22_2 Q2.hfix89_22_2 Q2.hinj89_22_2
      Q2.hcardT89_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_22_2 i) (Q2.hfix89_22_2 i) _)
      colCert_89_22_15.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T89_22
      hfix89_22 hinj89_22 hcardT89_22
      (fun i => conj_mem_of_fixedPoints _ _ (T89_22 i) (hfix89_22 i) _)
      ⟨89, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T89_22_2 Q2.hfix89_22_2 Q2.hinj89_22_2
      Q2.hcardT89_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_22_2 i) (Q2.hfix89_22_2 i) _)
      colCert_89_22_20.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T89_23
      hfix89_23 hinj89_23 hcardT89_23
      (fun i => conj_mem_of_fixedPoints _ _ (T89_23 i) (hfix89_23 i) _)
      ⟨89, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T89_23_2 Q2.hfix89_23_2 Q2.hinj89_23_2
      Q2.hcardT89_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_23_2 i) (Q2.hfix89_23_2 i) _)
      colCert_89_23_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T89_23
      hfix89_23 hinj89_23 hcardT89_23
      (fun i => conj_mem_of_fixedPoints _ _ (T89_23 i) (hfix89_23 i) _)
      ⟨89, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T89_23_2 Q2.hfix89_23_2 Q2.hinj89_23_2
      Q2.hcardT89_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_23_2 i) (Q2.hfix89_23_2 i) _)
      colCert_89_23_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T89_23
      hfix89_23 hinj89_23 hcardT89_23
      (fun i => conj_mem_of_fixedPoints _ _ (T89_23 i) (hfix89_23 i) _)
      ⟨89, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T89_23_2 Q2.hfix89_23_2 Q2.hinj89_23_2
      Q2.hcardT89_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_23_2 i) (Q2.hfix89_23_2 i) _)
      colCert_89_23_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T89_23
      hfix89_23 hinj89_23 hcardT89_23
      (fun i => conj_mem_of_fixedPoints _ _ (T89_23 i) (hfix89_23 i) _)
      ⟨89, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T89_23_2 Q2.hfix89_23_2 Q2.hinj89_23_2
      Q2.hcardT89_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_23_2 i) (Q2.hfix89_23_2 i) _)
      colCert_89_23_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T89_23
      hfix89_23 hinj89_23 hcardT89_23
      (fun i => conj_mem_of_fixedPoints _ _ (T89_23 i) (hfix89_23 i) _)
      ⟨89, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T89_23_2 Q2.hfix89_23_2 Q2.hinj89_23_2
      Q2.hcardT89_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_23_2 i) (Q2.hfix89_23_2 i) _)
      colCert_89_23_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T89_23
      hfix89_23 hinj89_23 hcardT89_23
      (fun i => conj_mem_of_fixedPoints _ _ (T89_23 i) (hfix89_23 i) _)
      ⟨89, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T89_23_2 Q2.hfix89_23_2 Q2.hinj89_23_2
      Q2.hcardT89_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_23_2 i) (Q2.hfix89_23_2 i) _)
      colCert_89_23_5.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T89_23
      hfix89_23 hinj89_23 hcardT89_23
      (fun i => conj_mem_of_fixedPoints _ _ (T89_23 i) (hfix89_23 i) _)
      ⟨89, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T89_23_2 Q2.hfix89_23_2 Q2.hinj89_23_2
      Q2.hcardT89_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_23_2 i) (Q2.hfix89_23_2 i) _)
      colCert_89_23_10.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T89_23
      hfix89_23 hinj89_23 hcardT89_23
      (fun i => conj_mem_of_fixedPoints _ _ (T89_23 i) (hfix89_23 i) _)
      ⟨89, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T89_23_2 Q2.hfix89_23_2 Q2.hinj89_23_2
      Q2.hcardT89_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_23_2 i) (Q2.hfix89_23_2 i) _)
      colCert_89_23_15.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T89_23
      hfix89_23 hinj89_23 hcardT89_23
      (fun i => conj_mem_of_fixedPoints _ _ (T89_23 i) (hfix89_23 i) _)
      ⟨89, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T89_23_2 Q2.hfix89_23_2 Q2.hinj89_23_2
      Q2.hcardT89_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_23_2 i) (Q2.hfix89_23_2 i) _)
      colCert_89_23_20.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T89_26
      hfix89_26 hinj89_26 hcardT89_26
      (fun i => conj_mem_of_fixedPoints _ _ (T89_26 i) (hfix89_26 i) _)
      ⟨89, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T89_26_2 Q2.hfix89_26_2 Q2.hinj89_26_2
      Q2.hcardT89_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_26_2 i) (Q2.hfix89_26_2 i) _)
      colCert_89_26_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T89_26
      hfix89_26 hinj89_26 hcardT89_26
      (fun i => conj_mem_of_fixedPoints _ _ (T89_26 i) (hfix89_26 i) _)
      ⟨89, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T89_26_2 Q2.hfix89_26_2 Q2.hinj89_26_2
      Q2.hcardT89_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_26_2 i) (Q2.hfix89_26_2 i) _)
      colCert_89_26_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T89_26
      hfix89_26 hinj89_26 hcardT89_26
      (fun i => conj_mem_of_fixedPoints _ _ (T89_26 i) (hfix89_26 i) _)
      ⟨89, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T89_26_2 Q2.hfix89_26_2 Q2.hinj89_26_2
      Q2.hcardT89_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_26_2 i) (Q2.hfix89_26_2 i) _)
      colCert_89_26_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T89_26
      hfix89_26 hinj89_26 hcardT89_26
      (fun i => conj_mem_of_fixedPoints _ _ (T89_26 i) (hfix89_26 i) _)
      ⟨89, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T89_26_2 Q2.hfix89_26_2 Q2.hinj89_26_2
      Q2.hcardT89_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_26_2 i) (Q2.hfix89_26_2 i) _)
      colCert_89_26_3.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T89_26
      hfix89_26 hinj89_26 hcardT89_26
      (fun i => conj_mem_of_fixedPoints _ _ (T89_26 i) (hfix89_26 i) _)
      ⟨89, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T89_26_2 Q2.hfix89_26_2 Q2.hinj89_26_2
      Q2.hcardT89_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_26_2 i) (Q2.hfix89_26_2 i) _)
      colCert_89_26_4.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T89_26
      hfix89_26 hinj89_26 hcardT89_26
      (fun i => conj_mem_of_fixedPoints _ _ (T89_26 i) (hfix89_26 i) _)
      ⟨89, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T89_26_2 Q2.hfix89_26_2 Q2.hinj89_26_2
      Q2.hcardT89_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_26_2 i) (Q2.hfix89_26_2 i) _)
      colCert_89_26_5.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T89_26
      hfix89_26 hinj89_26 hcardT89_26
      (fun i => conj_mem_of_fixedPoints _ _ (T89_26 i) (hfix89_26 i) _)
      ⟨89, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T89_26_2 Q2.hfix89_26_2 Q2.hinj89_26_2
      Q2.hcardT89_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_26_2 i) (Q2.hfix89_26_2 i) _)
      colCert_89_26_10.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T89_26
      hfix89_26 hinj89_26 hcardT89_26
      (fun i => conj_mem_of_fixedPoints _ _ (T89_26 i) (hfix89_26 i) _)
      ⟨89, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T89_26_2 Q2.hfix89_26_2 Q2.hinj89_26_2
      Q2.hcardT89_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_26_2 i) (Q2.hfix89_26_2 i) _)
      colCert_89_26_15.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T89_26
      hfix89_26 hinj89_26 hcardT89_26
      (fun i => conj_mem_of_fixedPoints _ _ (T89_26 i) (hfix89_26 i) _)
      ⟨89, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T89_26_2 Q2.hfix89_26_2 Q2.hinj89_26_2
      Q2.hcardT89_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_26_2 i) (Q2.hfix89_26_2 i) _)
      colCert_89_26_20.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T89_54
      hfix89_54 hinj89_54 hcardT89_54
      (fun i => conj_mem_of_fixedPoints _ _ (T89_54 i) (hfix89_54 i) _)
      ⟨89, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T89_54_2 Q2.hfix89_54_2 Q2.hinj89_54_2
      Q2.hcardT89_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_54_2 i) (Q2.hfix89_54_2 i) _)
      colCert_89_54_0.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T89_54
      hfix89_54 hinj89_54 hcardT89_54
      (fun i => conj_mem_of_fixedPoints _ _ (T89_54 i) (hfix89_54 i) _)
      ⟨89, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T89_54_2 Q2.hfix89_54_2 Q2.hinj89_54_2
      Q2.hcardT89_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_54_2 i) (Q2.hfix89_54_2 i) _)
      colCert_89_54_1.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T89_54
      hfix89_54 hinj89_54 hcardT89_54
      (fun i => conj_mem_of_fixedPoints _ _ (T89_54 i) (hfix89_54 i) _)
      ⟨89, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T89_54_2 Q2.hfix89_54_2 Q2.hinj89_54_2
      Q2.hcardT89_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_54_2 i) (Q2.hfix89_54_2 i) _)
      colCert_89_54_2.hD ?_).symm
  rw [alnId_89 j hj]


theorem leaf_89_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 89 []).length)
    (hq : (normIsRep.getD 89 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨89, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨89, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨89, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨89, by decide⟩ (listedAt ⟨89, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T89_54
      hfix89_54 hinj89_54 hcardT89_54
      (fun i => conj_mem_of_fixedPoints _ _ (T89_54 i) (hfix89_54 i) _)
      ⟨89, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨89, by decide⟩ (Q2.listedAt ⟨89, by decide⟩
        (alnCheck_rep ⟨89, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T89_54_2 Q2.hfix89_54_2 Q2.hinj89_54_2
      Q2.hcardT89_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T89_54_2 i) (Q2.hfix89_54_2 i) _)
      colCert_89_54_3.hD ?_).symm
  rw [alnId_89 j hj]


end LeanDring.P5Presentation
