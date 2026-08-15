/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C182
import LeanDring.P5.Data.ColRestCheap.C183
import LeanDring.P5.Data.ColRestCheap.C184
import LeanDring.P5.Data.ColRestCheap.C185
import LeanDring.P5.Data.ColRestCheap.C186
import LeanDring.P5.Data.ColTau.C004
import LeanDring.P5.Data.EntryK.C020
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk01
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk02

/-! # Stage-5 leaves, chunk 15 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_85_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T85_22
      hfix85_22 hinj85_22 hcardT85_22
      (fun i => conj_mem_of_fixedPoints _ _ (T85_22 i) (hfix85_22 i) _)
      ⟨85, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T85_22_2 Q2.hfix85_22_2 Q2.hinj85_22_2
      Q2.hcardT85_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_22_2 i) (Q2.hfix85_22_2 i) _)
      colCert_85_22_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T85_22
      hfix85_22 hinj85_22 hcardT85_22
      (fun i => conj_mem_of_fixedPoints _ _ (T85_22 i) (hfix85_22 i) _)
      ⟨85, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T85_22_2 Q2.hfix85_22_2 Q2.hinj85_22_2
      Q2.hcardT85_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_22_2 i) (Q2.hfix85_22_2 i) _)
      colCert_85_22_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T85_23
      hfix85_23 hinj85_23 hcardT85_23
      (fun i => conj_mem_of_fixedPoints _ _ (T85_23 i) (hfix85_23 i) _)
      ⟨85, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T85_23_2 Q2.hfix85_23_2 Q2.hinj85_23_2
      Q2.hcardT85_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_23_2 i) (Q2.hfix85_23_2 i) _)
      colCert_85_23_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T85_23
      hfix85_23 hinj85_23 hcardT85_23
      (fun i => conj_mem_of_fixedPoints _ _ (T85_23 i) (hfix85_23 i) _)
      ⟨85, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T85_23_2 Q2.hfix85_23_2 Q2.hinj85_23_2
      Q2.hcardT85_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_23_2 i) (Q2.hfix85_23_2 i) _)
      colCert_85_23_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T85_23
      hfix85_23 hinj85_23 hcardT85_23
      (fun i => conj_mem_of_fixedPoints _ _ (T85_23 i) (hfix85_23 i) _)
      ⟨85, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T85_23_2 Q2.hfix85_23_2 Q2.hinj85_23_2
      Q2.hcardT85_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_23_2 i) (Q2.hfix85_23_2 i) _)
      colCert_85_23_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T85_23
      hfix85_23 hinj85_23 hcardT85_23
      (fun i => conj_mem_of_fixedPoints _ _ (T85_23 i) (hfix85_23 i) _)
      ⟨85, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T85_23_2 Q2.hfix85_23_2 Q2.hinj85_23_2
      Q2.hcardT85_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_23_2 i) (Q2.hfix85_23_2 i) _)
      colCert_85_23_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T85_23
      hfix85_23 hinj85_23 hcardT85_23
      (fun i => conj_mem_of_fixedPoints _ _ (T85_23 i) (hfix85_23 i) _)
      ⟨85, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T85_23_2 Q2.hfix85_23_2 Q2.hinj85_23_2
      Q2.hcardT85_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_23_2 i) (Q2.hfix85_23_2 i) _)
      colCert_85_23_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T85_23
      hfix85_23 hinj85_23 hcardT85_23
      (fun i => conj_mem_of_fixedPoints _ _ (T85_23 i) (hfix85_23 i) _)
      ⟨85, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T85_23_2 Q2.hfix85_23_2 Q2.hinj85_23_2
      Q2.hcardT85_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_23_2 i) (Q2.hfix85_23_2 i) _)
      colCert_85_23_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T85_23
      hfix85_23 hinj85_23 hcardT85_23
      (fun i => conj_mem_of_fixedPoints _ _ (T85_23 i) (hfix85_23 i) _)
      ⟨85, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T85_23_2 Q2.hfix85_23_2 Q2.hinj85_23_2
      Q2.hcardT85_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_23_2 i) (Q2.hfix85_23_2 i) _)
      colCert_85_23_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T85_23
      hfix85_23 hinj85_23 hcardT85_23
      (fun i => conj_mem_of_fixedPoints _ _ (T85_23 i) (hfix85_23 i) _)
      ⟨85, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T85_23_2 Q2.hfix85_23_2 Q2.hinj85_23_2
      Q2.hcardT85_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_23_2 i) (Q2.hfix85_23_2 i) _)
      colCert_85_23_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T85_23
      hfix85_23 hinj85_23 hcardT85_23
      (fun i => conj_mem_of_fixedPoints _ _ (T85_23 i) (hfix85_23 i) _)
      ⟨85, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T85_23_2 Q2.hfix85_23_2 Q2.hinj85_23_2
      Q2.hcardT85_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_23_2 i) (Q2.hfix85_23_2 i) _)
      colCert_85_23_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T85_27
      hfix85_27 hinj85_27 hcardT85_27
      (fun i => conj_mem_of_fixedPoints _ _ (T85_27 i) (hfix85_27 i) _)
      ⟨85, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T85_27_2 Q2.hfix85_27_2 Q2.hinj85_27_2
      Q2.hcardT85_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_27_2 i) (Q2.hfix85_27_2 i) _)
      colCert_85_27_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T85_27
      hfix85_27 hinj85_27 hcardT85_27
      (fun i => conj_mem_of_fixedPoints _ _ (T85_27 i) (hfix85_27 i) _)
      ⟨85, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T85_27_2 Q2.hfix85_27_2 Q2.hinj85_27_2
      Q2.hcardT85_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_27_2 i) (Q2.hfix85_27_2 i) _)
      colCert_85_27_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T85_27
      hfix85_27 hinj85_27 hcardT85_27
      (fun i => conj_mem_of_fixedPoints _ _ (T85_27 i) (hfix85_27 i) _)
      ⟨85, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T85_27_2 Q2.hfix85_27_2 Q2.hinj85_27_2
      Q2.hcardT85_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_27_2 i) (Q2.hfix85_27_2 i) _)
      colCert_85_27_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T85_27
      hfix85_27 hinj85_27 hcardT85_27
      (fun i => conj_mem_of_fixedPoints _ _ (T85_27 i) (hfix85_27 i) _)
      ⟨85, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T85_27_2 Q2.hfix85_27_2 Q2.hinj85_27_2
      Q2.hcardT85_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_27_2 i) (Q2.hfix85_27_2 i) _)
      colCert_85_27_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T85_27
      hfix85_27 hinj85_27 hcardT85_27
      (fun i => conj_mem_of_fixedPoints _ _ (T85_27 i) (hfix85_27 i) _)
      ⟨85, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T85_27_2 Q2.hfix85_27_2 Q2.hinj85_27_2
      Q2.hcardT85_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_27_2 i) (Q2.hfix85_27_2 i) _)
      colCert_85_27_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T85_27
      hfix85_27 hinj85_27 hcardT85_27
      (fun i => conj_mem_of_fixedPoints _ _ (T85_27 i) (hfix85_27 i) _)
      ⟨85, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T85_27_2 Q2.hfix85_27_2 Q2.hinj85_27_2
      Q2.hcardT85_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_27_2 i) (Q2.hfix85_27_2 i) _)
      colCert_85_27_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T85_27
      hfix85_27 hinj85_27 hcardT85_27
      (fun i => conj_mem_of_fixedPoints _ _ (T85_27 i) (hfix85_27 i) _)
      ⟨85, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T85_27_2 Q2.hfix85_27_2 Q2.hinj85_27_2
      Q2.hcardT85_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_27_2 i) (Q2.hfix85_27_2 i) _)
      colCert_85_27_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T85_27
      hfix85_27 hinj85_27 hcardT85_27
      (fun i => conj_mem_of_fixedPoints _ _ (T85_27 i) (hfix85_27 i) _)
      ⟨85, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T85_27_2 Q2.hfix85_27_2 Q2.hinj85_27_2
      Q2.hcardT85_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_27_2 i) (Q2.hfix85_27_2 i) _)
      colCert_85_27_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T85_27
      hfix85_27 hinj85_27 hcardT85_27
      (fun i => conj_mem_of_fixedPoints _ _ (T85_27 i) (hfix85_27 i) _)
      ⟨85, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T85_27_2 Q2.hfix85_27_2 Q2.hinj85_27_2
      Q2.hcardT85_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_27_2 i) (Q2.hfix85_27_2 i) _)
      colCert_85_27_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T85_54
      hfix85_54 hinj85_54 hcardT85_54
      (fun i => conj_mem_of_fixedPoints _ _ (T85_54 i) (hfix85_54 i) _)
      ⟨85, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T85_54_2 Q2.hfix85_54_2 Q2.hinj85_54_2
      Q2.hcardT85_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_54_2 i) (Q2.hfix85_54_2 i) _)
      colCert_85_54_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T85_54
      hfix85_54 hinj85_54 hcardT85_54
      (fun i => conj_mem_of_fixedPoints _ _ (T85_54 i) (hfix85_54 i) _)
      ⟨85, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T85_54_2 Q2.hfix85_54_2 Q2.hinj85_54_2
      Q2.hcardT85_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_54_2 i) (Q2.hfix85_54_2 i) _)
      colCert_85_54_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T85_54
      hfix85_54 hinj85_54 hcardT85_54
      (fun i => conj_mem_of_fixedPoints _ _ (T85_54 i) (hfix85_54 i) _)
      ⟨85, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T85_54_2 Q2.hfix85_54_2 Q2.hinj85_54_2
      Q2.hcardT85_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_54_2 i) (Q2.hfix85_54_2 i) _)
      colCert_85_54_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T85_54
      hfix85_54 hinj85_54 hcardT85_54
      (fun i => conj_mem_of_fixedPoints _ _ (T85_54 i) (hfix85_54 i) _)
      ⟨85, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T85_54_2 Q2.hfix85_54_2 Q2.hinj85_54_2
      Q2.hcardT85_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_54_2 i) (Q2.hfix85_54_2 i) _)
      colCert_85_54_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T85_54
      hfix85_54 hinj85_54 hcardT85_54
      (fun i => conj_mem_of_fixedPoints _ _ (T85_54 i) (hfix85_54 i) _)
      ⟨85, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T85_54_2 Q2.hfix85_54_2 Q2.hinj85_54_2
      Q2.hcardT85_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_54_2 i) (Q2.hfix85_54_2 i) _)
      colCert_85_54_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T85_54
      hfix85_54 hinj85_54 hcardT85_54
      (fun i => conj_mem_of_fixedPoints _ _ (T85_54 i) (hfix85_54 i) _)
      ⟨85, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T85_54_2 Q2.hfix85_54_2 Q2.hinj85_54_2
      Q2.hcardT85_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_54_2 i) (Q2.hfix85_54_2 i) _)
      colCert_85_54_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T85_54
      hfix85_54 hinj85_54 hcardT85_54
      (fun i => conj_mem_of_fixedPoints _ _ (T85_54 i) (hfix85_54 i) _)
      ⟨85, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T85_54_2 Q2.hfix85_54_2 Q2.hinj85_54_2
      Q2.hcardT85_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_54_2 i) (Q2.hfix85_54_2 i) _)
      colCert_85_54_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T85_54
      hfix85_54 hinj85_54 hcardT85_54
      (fun i => conj_mem_of_fixedPoints _ _ (T85_54 i) (hfix85_54 i) _)
      ⟨85, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T85_54_2 Q2.hfix85_54_2 Q2.hinj85_54_2
      Q2.hcardT85_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_54_2 i) (Q2.hfix85_54_2 i) _)
      colCert_85_54_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T85_54
      hfix85_54 hinj85_54 hcardT85_54
      (fun i => conj_mem_of_fixedPoints _ _ (T85_54 i) (hfix85_54 i) _)
      ⟨85, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T85_54_2 Q2.hfix85_54_2 Q2.hinj85_54_2
      Q2.hcardT85_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_54_2 i) (Q2.hfix85_54_2 i) _)
      colCert_85_54_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_0 (hp : 0 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 0 (transLenTr ⟨85, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 0 (transLenTr ⟨85, by decide⟩ 0 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 0 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_1 (hp : 1 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 1 (transLenTr ⟨85, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 1 (transLenTr ⟨85, by decide⟩ 1 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 1 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_2 (hp : 2 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 2 (transLenTr ⟨85, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 2 (transLenTr ⟨85, by decide⟩ 2 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 2 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_3 (hp : 3 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 3 (transLenTr ⟨85, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 3 (transLenTr ⟨85, by decide⟩ 3 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 3 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_4 (hp : 4 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 4 (transLenTr ⟨85, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 4 (transLenTr ⟨85, by decide⟩ 4 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 4 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_5 (hp : 5 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 5 (transLenTr ⟨85, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 5 (transLenTr ⟨85, by decide⟩ 5 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 5 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_6 (hp : 6 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 6 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 6 (transLenTr ⟨85, by decide⟩ 6 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 6 (transLenTr ⟨85, by decide⟩ 6 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 6 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_6.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_7 (hp : 7 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 7 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 7 (transLenTr ⟨85, by decide⟩ 7 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 7 (transLenTr ⟨85, by decide⟩ 7 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 7 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_7.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_8 (hp : 8 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 8 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 8 (transLenTr ⟨85, by decide⟩ 8 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 8 (transLenTr ⟨85, by decide⟩ 8 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 8 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_8.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_9 (hp : 9 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 9 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 9 (transLenTr ⟨85, by decide⟩ 9 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 9 (transLenTr ⟨85, by decide⟩ 9 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 9 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_9.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_10 (hp : 10 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 10 (transLenTr ⟨85, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 10 (transLenTr ⟨85, by decide⟩ 10 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 10 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_11 (hp : 11 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 11 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 11 (transLenTr ⟨85, by decide⟩ 11 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 11 (transLenTr ⟨85, by decide⟩ 11 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 11 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_11.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_12 (hp : 12 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 12 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 12 (transLenTr ⟨85, by decide⟩ 12 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 12 (transLenTr ⟨85, by decide⟩ 12 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 12 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_12.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_13 (hp : 13 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 13 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 13 (transLenTr ⟨85, by decide⟩ 13 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 13 (transLenTr ⟨85, by decide⟩ 13 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 13 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_13.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_14 (hp : 14 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 14 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 14 (transLenTr ⟨85, by decide⟩ 14 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 14 (transLenTr ⟨85, by decide⟩ 14 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 14 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_14.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_15 (hp : 15 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 15 (transLenTr ⟨85, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 15 (transLenTr ⟨85, by decide⟩ 15 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 15 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_16 (hp : 16 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 16 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 16 (transLenTr ⟨85, by decide⟩ 16 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 16 (transLenTr ⟨85, by decide⟩ 16 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 16 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_16.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_17 (hp : 17 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 17 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 17 (transLenTr ⟨85, by decide⟩ 17 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 17 (transLenTr ⟨85, by decide⟩ 17 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 17 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_17.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_18 (hp : 18 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 18 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 18 (transLenTr ⟨85, by decide⟩ 18 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 18 (transLenTr ⟨85, by decide⟩ 18 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 18 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_18.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_19 (hp : 19 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 19 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 19 (transLenTr ⟨85, by decide⟩ 19 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 19 (transLenTr ⟨85, by decide⟩ 19 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 19 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_19.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_20 (hp : 20 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 20 (transLenTr ⟨85, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 20 (transLenTr ⟨85, by decide⟩ 20 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 20 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_21 (hp : 21 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 21 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 21 (transLenTr ⟨85, by decide⟩ 21 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 21 (transLenTr ⟨85, by decide⟩ 21 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 21 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_21.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_22 (hp : 22 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 22 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 22 (transLenTr ⟨85, by decide⟩ 22 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 22 (transLenTr ⟨85, by decide⟩ 22 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 22 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_22.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_23 (hp : 23 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 23 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 23 (transLenTr ⟨85, by decide⟩ 23 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 23 (transLenTr ⟨85, by decide⟩ 23 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 23 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_23.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_24 (hp : 24 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 24 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 24 (transLenTr ⟨85, by decide⟩ 24 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 24 (transLenTr ⟨85, by decide⟩ 24 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 24 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_24.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_25 (hp : 25 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 25 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 25 (transLenTr ⟨85, by decide⟩ 25 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 25 (transLenTr ⟨85, by decide⟩ 25 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 25 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_25.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_30 (hp : 30 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 30 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 30 (transLenTr ⟨85, by decide⟩ 30 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 30 (transLenTr ⟨85, by decide⟩ 30 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 30 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_30.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_35 (hp : 35 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 35 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 35 (transLenTr ⟨85, by decide⟩ 35 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 35 (transLenTr ⟨85, by decide⟩ 35 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 35 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_35.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_40 (hp : 40 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 40 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 40 (transLenTr ⟨85, by decide⟩ 40 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 40 (transLenTr ⟨85, by decide⟩ 40 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 40 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_40.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_45 (hp : 45 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 45 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 45 (transLenTr ⟨85, by decide⟩ 45 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 45 (transLenTr ⟨85, by decide⟩ 45 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 45 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      colCert_85_85_45.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_85_50 (hp : 50 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 50 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 50 (transLenTr ⟨85, by decide⟩ 50 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 50 (transLenTr ⟨85, by decide⟩ 50 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 50 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 50 (transLenTr ⟨85, by decide⟩ 50 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_50.D1 (m := 5) from colCertDiv_85_85_50.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 50 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_50.D2 (m := 5) from colCertDiv_85_85_50.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_50_tau_match


theorem leaf_85_85_55 (hp : 55 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 55 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 55 (transLenTr ⟨85, by decide⟩ 55 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 55 (transLenTr ⟨85, by decide⟩ 55 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 55 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 55 (transLenTr ⟨85, by decide⟩ 55 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_55.D1 (m := 5) from colCertDiv_85_85_55.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 55 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_55.D2 (m := 5) from colCertDiv_85_85_55.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_55_tau_match


theorem leaf_85_85_60 (hp : 60 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 60 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 60 (transLenTr ⟨85, by decide⟩ 60 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 60 (transLenTr ⟨85, by decide⟩ 60 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 60 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 60 (transLenTr ⟨85, by decide⟩ 60 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_60.D1 (m := 5) from colCertDiv_85_85_60.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 60 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_60.D2 (m := 5) from colCertDiv_85_85_60.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_60_tau_match


theorem leaf_85_85_65 (hp : 65 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 65 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 65 (transLenTr ⟨85, by decide⟩ 65 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 65 (transLenTr ⟨85, by decide⟩ 65 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 65 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 65 (transLenTr ⟨85, by decide⟩ 65 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_65.D1 (m := 5) from colCertDiv_85_85_65.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 65 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_65.D2 (m := 5) from colCertDiv_85_85_65.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_65_tau_match


theorem leaf_85_85_70 (hp : 70 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 70 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 70 (transLenTr ⟨85, by decide⟩ 70 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 70 (transLenTr ⟨85, by decide⟩ 70 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 70 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 70 (transLenTr ⟨85, by decide⟩ 70 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_70.D1 (m := 5) from colCertDiv_85_85_70.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 70 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_70.D2 (m := 5) from colCertDiv_85_85_70.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_70_tau_match


theorem leaf_85_85_75 (hp : 75 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 75 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 75 (transLenTr ⟨85, by decide⟩ 75 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 75 (transLenTr ⟨85, by decide⟩ 75 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 75 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 75 (transLenTr ⟨85, by decide⟩ 75 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_75.D1 (m := 5) from colCertDiv_85_85_75.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 75 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_75.D2 (m := 5) from colCertDiv_85_85_75.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_75_tau_match


theorem leaf_85_85_80 (hp : 80 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 80 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 80 (transLenTr ⟨85, by decide⟩ 80 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 80 (transLenTr ⟨85, by decide⟩ 80 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 80 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 80 (transLenTr ⟨85, by decide⟩ 80 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_80.D1 (m := 5) from colCertDiv_85_85_80.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 80 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_80.D2 (m := 5) from colCertDiv_85_85_80.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_80_tau_match


theorem leaf_85_85_85 (hp : 85 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 85 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 85 (transLenTr ⟨85, by decide⟩ 85 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 85 (transLenTr ⟨85, by decide⟩ 85 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 85 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 85 (transLenTr ⟨85, by decide⟩ 85 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_85.D1 (m := 5) from colCertDiv_85_85_85.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 85 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_85.D2 (m := 5) from colCertDiv_85_85_85.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_85_tau_match


theorem leaf_85_85_90 (hp : 90 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 90 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 90 (transLenTr ⟨85, by decide⟩ 90 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 90 (transLenTr ⟨85, by decide⟩ 90 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 90 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 90 (transLenTr ⟨85, by decide⟩ 90 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_90.D1 (m := 5) from colCertDiv_85_85_90.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 90 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_90.D2 (m := 5) from colCertDiv_85_85_90.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_90_tau_match


theorem leaf_85_85_95 (hp : 95 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 95 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 95 (transLenTr ⟨85, by decide⟩ 95 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 95 (transLenTr ⟨85, by decide⟩ 95 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 95 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 95 (transLenTr ⟨85, by decide⟩ 95 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_95.D1 (m := 5) from colCertDiv_85_85_95.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 95 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_95.D2 (m := 5) from colCertDiv_85_85_95.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_95_tau_match


theorem leaf_85_85_100 (hp : 100 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 100 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 100 (transLenTr ⟨85, by decide⟩ 100 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 100 (transLenTr ⟨85, by decide⟩ 100 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 100 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 100 (transLenTr ⟨85, by decide⟩ 100 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_100.D1 (m := 5) from colCertDiv_85_85_100.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 100 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_100.D2 (m := 5) from colCertDiv_85_85_100.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_100_tau_match


theorem leaf_85_85_105 (hp : 105 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 105 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 105 (transLenTr ⟨85, by decide⟩ 105 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 105 (transLenTr ⟨85, by decide⟩ 105 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 105 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 105 (transLenTr ⟨85, by decide⟩ 105 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_105.D1 (m := 5) from colCertDiv_85_85_105.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 105 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_105.D2 (m := 5) from colCertDiv_85_85_105.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_105_tau_match


theorem leaf_85_85_110 (hp : 110 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 110 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 110 (transLenTr ⟨85, by decide⟩ 110 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 110 (transLenTr ⟨85, by decide⟩ 110 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 110 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 110 (transLenTr ⟨85, by decide⟩ 110 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_110.D1 (m := 5) from colCertDiv_85_85_110.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 110 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_110.D2 (m := 5) from colCertDiv_85_85_110.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_110_tau_match


theorem leaf_85_85_115 (hp : 115 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 115 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 115 (transLenTr ⟨85, by decide⟩ 115 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 115 (transLenTr ⟨85, by decide⟩ 115 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 115 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 115 (transLenTr ⟨85, by decide⟩ 115 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_115.D1 (m := 5) from colCertDiv_85_85_115.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 115 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_115.D2 (m := 5) from colCertDiv_85_85_115.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_115_tau_match


theorem leaf_85_85_120 (hp : 120 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 120 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 120 (transLenTr ⟨85, by decide⟩ 120 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨85, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 120 (transLenTr ⟨85, by decide⟩ 120 hp)) T85_85
      hfix85_85 hinj85_85 hcardT85_85
      (fun i => conj_mem_of_fixedPoints _ _ (T85_85 i) (hfix85_85 i) _)
      ⟨85, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 120 hp) Q2.T85_85_2 Q2.hfix85_85_2 Q2.hinj85_85_2
      Q2.hcardT85_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_85_2 i) (Q2.hfix85_85_2 i) _)
      ?_).symm
  rw [show colData1 (⟨85, by decide⟩ : Fin 148)
        ((colE1 ⟨85, by decide⟩ 120 (transLenTr ⟨85, by decide⟩ 120 hp) : ↥(reps ⟨85, by decide⟩)) : Coordinate 1)
        T85_85 = colFn colCertDiv_85_85_120.D1 (m := 5) from colCertDiv_85_85_120.bind1,
    show colData2 (⟨85, by decide⟩ : Fin 148)
        ((colE2 ⟨85, by decide⟩ 120 hp : ↥(Q2.reps ⟨85, by decide⟩)) : Coordinate 2)
        Q2.T85_85_2 = colFn colCertDiv_85_85_120.D2 (m := 5) from colCertDiv_85_85_120.bind2]
  rw [alnId_85 j hj]
  exact fastcode_of_tau ⟨85, by decide⟩ _ _ _
    ((alnId_85 j hj) ▸ Q2.listedAt (⟨85, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨85, by decide⟩ : Fin 148) hj hq).1) colCertDiv_85_85_120_tau_match


theorem leaf_86_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T86_1
      hfix86_1 hinj86_1 hcardT86_1
      (fun i => conj_mem_of_fixedPoints _ _ (T86_1 i) (hfix86_1 i) _)
      ⟨86, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T86_1_2 Q2.hfix86_1_2 Q2.hinj86_1_2
      Q2.hcardT86_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_1_2 i) (Q2.hfix86_1_2 i) _)
      colCert_86_1_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T86_1
      hfix86_1 hinj86_1 hcardT86_1
      (fun i => conj_mem_of_fixedPoints _ _ (T86_1 i) (hfix86_1 i) _)
      ⟨86, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T86_1_2 Q2.hfix86_1_2 Q2.hinj86_1_2
      Q2.hcardT86_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_1_2 i) (Q2.hfix86_1_2 i) _)
      colCert_86_1_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T86_1
      hfix86_1 hinj86_1 hcardT86_1
      (fun i => conj_mem_of_fixedPoints _ _ (T86_1 i) (hfix86_1 i) _)
      ⟨86, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T86_1_2 Q2.hfix86_1_2 Q2.hinj86_1_2
      Q2.hcardT86_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_1_2 i) (Q2.hfix86_1_2 i) _)
      colCert_86_1_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T86_1
      hfix86_1 hinj86_1 hcardT86_1
      (fun i => conj_mem_of_fixedPoints _ _ (T86_1 i) (hfix86_1 i) _)
      ⟨86, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T86_1_2 Q2.hfix86_1_2 Q2.hinj86_1_2
      Q2.hcardT86_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_1_2 i) (Q2.hfix86_1_2 i) _)
      colCert_86_1_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T86_1
      hfix86_1 hinj86_1 hcardT86_1
      (fun i => conj_mem_of_fixedPoints _ _ (T86_1 i) (hfix86_1 i) _)
      ⟨86, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T86_1_2 Q2.hfix86_1_2 Q2.hinj86_1_2
      Q2.hcardT86_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_1_2 i) (Q2.hfix86_1_2 i) _)
      colCert_86_1_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T86_2
      hfix86_2 hinj86_2 hcardT86_2
      (fun i => conj_mem_of_fixedPoints _ _ (T86_2 i) (hfix86_2 i) _)
      ⟨86, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T86_2_2 Q2.hfix86_2_2 Q2.hinj86_2_2
      Q2.hcardT86_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_2_2 i) (Q2.hfix86_2_2 i) _)
      colCert_86_2_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T86_2
      hfix86_2 hinj86_2 hcardT86_2
      (fun i => conj_mem_of_fixedPoints _ _ (T86_2 i) (hfix86_2 i) _)
      ⟨86, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T86_2_2 Q2.hfix86_2_2 Q2.hinj86_2_2
      Q2.hcardT86_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_2_2 i) (Q2.hfix86_2_2 i) _)
      colCert_86_2_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T86_2
      hfix86_2 hinj86_2 hcardT86_2
      (fun i => conj_mem_of_fixedPoints _ _ (T86_2 i) (hfix86_2 i) _)
      ⟨86, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T86_2_2 Q2.hfix86_2_2 Q2.hinj86_2_2
      Q2.hcardT86_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_2_2 i) (Q2.hfix86_2_2 i) _)
      colCert_86_2_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T86_2
      hfix86_2 hinj86_2 hcardT86_2
      (fun i => conj_mem_of_fixedPoints _ _ (T86_2 i) (hfix86_2 i) _)
      ⟨86, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T86_2_2 Q2.hfix86_2_2 Q2.hinj86_2_2
      Q2.hcardT86_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_2_2 i) (Q2.hfix86_2_2 i) _)
      colCert_86_2_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T86_2
      hfix86_2 hinj86_2 hcardT86_2
      (fun i => conj_mem_of_fixedPoints _ _ (T86_2 i) (hfix86_2 i) _)
      ⟨86, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T86_2_2 Q2.hfix86_2_2 Q2.hinj86_2_2
      Q2.hcardT86_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_2_2 i) (Q2.hfix86_2_2 i) _)
      colCert_86_2_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T86_3
      hfix86_3 hinj86_3 hcardT86_3
      (fun i => conj_mem_of_fixedPoints _ _ (T86_3 i) (hfix86_3 i) _)
      ⟨86, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T86_3_2 Q2.hfix86_3_2 Q2.hinj86_3_2
      Q2.hcardT86_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_3_2 i) (Q2.hfix86_3_2 i) _)
      colCert_86_3_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T86_3
      hfix86_3 hinj86_3 hcardT86_3
      (fun i => conj_mem_of_fixedPoints _ _ (T86_3 i) (hfix86_3 i) _)
      ⟨86, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T86_3_2 Q2.hfix86_3_2 Q2.hinj86_3_2
      Q2.hcardT86_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_3_2 i) (Q2.hfix86_3_2 i) _)
      colCert_86_3_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T86_3
      hfix86_3 hinj86_3 hcardT86_3
      (fun i => conj_mem_of_fixedPoints _ _ (T86_3 i) (hfix86_3 i) _)
      ⟨86, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T86_3_2 Q2.hfix86_3_2 Q2.hinj86_3_2
      Q2.hcardT86_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_3_2 i) (Q2.hfix86_3_2 i) _)
      colCert_86_3_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T86_3
      hfix86_3 hinj86_3 hcardT86_3
      (fun i => conj_mem_of_fixedPoints _ _ (T86_3 i) (hfix86_3 i) _)
      ⟨86, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T86_3_2 Q2.hfix86_3_2 Q2.hinj86_3_2
      Q2.hcardT86_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_3_2 i) (Q2.hfix86_3_2 i) _)
      colCert_86_3_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T86_3
      hfix86_3 hinj86_3 hcardT86_3
      (fun i => conj_mem_of_fixedPoints _ _ (T86_3 i) (hfix86_3 i) _)
      ⟨86, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T86_3_2 Q2.hfix86_3_2 Q2.hinj86_3_2
      Q2.hcardT86_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_3_2 i) (Q2.hfix86_3_2 i) _)
      colCert_86_3_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T86_4
      hfix86_4 hinj86_4 hcardT86_4
      (fun i => conj_mem_of_fixedPoints _ _ (T86_4 i) (hfix86_4 i) _)
      ⟨86, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T86_4_2 Q2.hfix86_4_2 Q2.hinj86_4_2
      Q2.hcardT86_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_4_2 i) (Q2.hfix86_4_2 i) _)
      colCert_86_4_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T86_4
      hfix86_4 hinj86_4 hcardT86_4
      (fun i => conj_mem_of_fixedPoints _ _ (T86_4 i) (hfix86_4 i) _)
      ⟨86, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T86_4_2 Q2.hfix86_4_2 Q2.hinj86_4_2
      Q2.hcardT86_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_4_2 i) (Q2.hfix86_4_2 i) _)
      colCert_86_4_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T86_4
      hfix86_4 hinj86_4 hcardT86_4
      (fun i => conj_mem_of_fixedPoints _ _ (T86_4 i) (hfix86_4 i) _)
      ⟨86, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T86_4_2 Q2.hfix86_4_2 Q2.hinj86_4_2
      Q2.hcardT86_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_4_2 i) (Q2.hfix86_4_2 i) _)
      colCert_86_4_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T86_4
      hfix86_4 hinj86_4 hcardT86_4
      (fun i => conj_mem_of_fixedPoints _ _ (T86_4 i) (hfix86_4 i) _)
      ⟨86, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T86_4_2 Q2.hfix86_4_2 Q2.hinj86_4_2
      Q2.hcardT86_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_4_2 i) (Q2.hfix86_4_2 i) _)
      colCert_86_4_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T86_4
      hfix86_4 hinj86_4 hcardT86_4
      (fun i => conj_mem_of_fixedPoints _ _ (T86_4 i) (hfix86_4 i) _)
      ⟨86, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T86_4_2 Q2.hfix86_4_2 Q2.hinj86_4_2
      Q2.hcardT86_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_4_2 i) (Q2.hfix86_4_2 i) _)
      colCert_86_4_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T86_5
      hfix86_5 hinj86_5 hcardT86_5
      (fun i => conj_mem_of_fixedPoints _ _ (T86_5 i) (hfix86_5 i) _)
      ⟨86, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T86_5_2 Q2.hfix86_5_2 Q2.hinj86_5_2
      Q2.hcardT86_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_5_2 i) (Q2.hfix86_5_2 i) _)
      colCert_86_5_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T86_5
      hfix86_5 hinj86_5 hcardT86_5
      (fun i => conj_mem_of_fixedPoints _ _ (T86_5 i) (hfix86_5 i) _)
      ⟨86, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T86_5_2 Q2.hfix86_5_2 Q2.hinj86_5_2
      Q2.hcardT86_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_5_2 i) (Q2.hfix86_5_2 i) _)
      colCert_86_5_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T86_5
      hfix86_5 hinj86_5 hcardT86_5
      (fun i => conj_mem_of_fixedPoints _ _ (T86_5 i) (hfix86_5 i) _)
      ⟨86, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T86_5_2 Q2.hfix86_5_2 Q2.hinj86_5_2
      Q2.hcardT86_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_5_2 i) (Q2.hfix86_5_2 i) _)
      colCert_86_5_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T86_5
      hfix86_5 hinj86_5 hcardT86_5
      (fun i => conj_mem_of_fixedPoints _ _ (T86_5 i) (hfix86_5 i) _)
      ⟨86, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T86_5_2 Q2.hfix86_5_2 Q2.hinj86_5_2
      Q2.hcardT86_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_5_2 i) (Q2.hfix86_5_2 i) _)
      colCert_86_5_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T86_5
      hfix86_5 hinj86_5 hcardT86_5
      (fun i => conj_mem_of_fixedPoints _ _ (T86_5 i) (hfix86_5 i) _)
      ⟨86, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T86_5_2 Q2.hfix86_5_2 Q2.hinj86_5_2
      Q2.hcardT86_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_5_2 i) (Q2.hfix86_5_2 i) _)
      colCert_86_5_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T86_11
      hfix86_11 hinj86_11 hcardT86_11
      (fun i => conj_mem_of_fixedPoints _ _ (T86_11 i) (hfix86_11 i) _)
      ⟨86, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T86_11_2 Q2.hfix86_11_2 Q2.hinj86_11_2
      Q2.hcardT86_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_11_2 i) (Q2.hfix86_11_2 i) _)
      colCert_86_11_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T86_11
      hfix86_11 hinj86_11 hcardT86_11
      (fun i => conj_mem_of_fixedPoints _ _ (T86_11 i) (hfix86_11 i) _)
      ⟨86, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T86_11_2 Q2.hfix86_11_2 Q2.hinj86_11_2
      Q2.hcardT86_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_11_2 i) (Q2.hfix86_11_2 i) _)
      colCert_86_11_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T86_11
      hfix86_11 hinj86_11 hcardT86_11
      (fun i => conj_mem_of_fixedPoints _ _ (T86_11 i) (hfix86_11 i) _)
      ⟨86, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T86_11_2 Q2.hfix86_11_2 Q2.hinj86_11_2
      Q2.hcardT86_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_11_2 i) (Q2.hfix86_11_2 i) _)
      colCert_86_11_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T86_11
      hfix86_11 hinj86_11 hcardT86_11
      (fun i => conj_mem_of_fixedPoints _ _ (T86_11 i) (hfix86_11 i) _)
      ⟨86, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T86_11_2 Q2.hfix86_11_2 Q2.hinj86_11_2
      Q2.hcardT86_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_11_2 i) (Q2.hfix86_11_2 i) _)
      colCert_86_11_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T86_11
      hfix86_11 hinj86_11 hcardT86_11
      (fun i => conj_mem_of_fixedPoints _ _ (T86_11 i) (hfix86_11 i) _)
      ⟨86, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T86_11_2 Q2.hfix86_11_2 Q2.hinj86_11_2
      Q2.hcardT86_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_11_2 i) (Q2.hfix86_11_2 i) _)
      colCert_86_11_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T86_12
      hfix86_12 hinj86_12 hcardT86_12
      (fun i => conj_mem_of_fixedPoints _ _ (T86_12 i) (hfix86_12 i) _)
      ⟨86, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T86_12_2 Q2.hfix86_12_2 Q2.hinj86_12_2
      Q2.hcardT86_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_12_2 i) (Q2.hfix86_12_2 i) _)
      colCert_86_12_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T86_12
      hfix86_12 hinj86_12 hcardT86_12
      (fun i => conj_mem_of_fixedPoints _ _ (T86_12 i) (hfix86_12 i) _)
      ⟨86, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T86_12_2 Q2.hfix86_12_2 Q2.hinj86_12_2
      Q2.hcardT86_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_12_2 i) (Q2.hfix86_12_2 i) _)
      colCert_86_12_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T86_12
      hfix86_12 hinj86_12 hcardT86_12
      (fun i => conj_mem_of_fixedPoints _ _ (T86_12 i) (hfix86_12 i) _)
      ⟨86, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T86_12_2 Q2.hfix86_12_2 Q2.hinj86_12_2
      Q2.hcardT86_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_12_2 i) (Q2.hfix86_12_2 i) _)
      colCert_86_12_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T86_12
      hfix86_12 hinj86_12 hcardT86_12
      (fun i => conj_mem_of_fixedPoints _ _ (T86_12 i) (hfix86_12 i) _)
      ⟨86, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T86_12_2 Q2.hfix86_12_2 Q2.hinj86_12_2
      Q2.hcardT86_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_12_2 i) (Q2.hfix86_12_2 i) _)
      colCert_86_12_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T86_12
      hfix86_12 hinj86_12 hcardT86_12
      (fun i => conj_mem_of_fixedPoints _ _ (T86_12 i) (hfix86_12 i) _)
      ⟨86, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T86_12_2 Q2.hfix86_12_2 Q2.hinj86_12_2
      Q2.hcardT86_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_12_2 i) (Q2.hfix86_12_2 i) _)
      colCert_86_12_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T86_19
      hfix86_19 hinj86_19 hcardT86_19
      (fun i => conj_mem_of_fixedPoints _ _ (T86_19 i) (hfix86_19 i) _)
      ⟨86, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T86_19_2 Q2.hfix86_19_2 Q2.hinj86_19_2
      Q2.hcardT86_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_19_2 i) (Q2.hfix86_19_2 i) _)
      colCert_86_19_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T86_19
      hfix86_19 hinj86_19 hcardT86_19
      (fun i => conj_mem_of_fixedPoints _ _ (T86_19 i) (hfix86_19 i) _)
      ⟨86, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T86_19_2 Q2.hfix86_19_2 Q2.hinj86_19_2
      Q2.hcardT86_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_19_2 i) (Q2.hfix86_19_2 i) _)
      colCert_86_19_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T86_19
      hfix86_19 hinj86_19 hcardT86_19
      (fun i => conj_mem_of_fixedPoints _ _ (T86_19 i) (hfix86_19 i) _)
      ⟨86, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T86_19_2 Q2.hfix86_19_2 Q2.hinj86_19_2
      Q2.hcardT86_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_19_2 i) (Q2.hfix86_19_2 i) _)
      colCert_86_19_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T86_19
      hfix86_19 hinj86_19 hcardT86_19
      (fun i => conj_mem_of_fixedPoints _ _ (T86_19 i) (hfix86_19 i) _)
      ⟨86, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T86_19_2 Q2.hfix86_19_2 Q2.hinj86_19_2
      Q2.hcardT86_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_19_2 i) (Q2.hfix86_19_2 i) _)
      colCert_86_19_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T86_19
      hfix86_19 hinj86_19 hcardT86_19
      (fun i => conj_mem_of_fixedPoints _ _ (T86_19 i) (hfix86_19 i) _)
      ⟨86, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T86_19_2 Q2.hfix86_19_2 Q2.hinj86_19_2
      Q2.hcardT86_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_19_2 i) (Q2.hfix86_19_2 i) _)
      colCert_86_19_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T86_19
      hfix86_19 hinj86_19 hcardT86_19
      (fun i => conj_mem_of_fixedPoints _ _ (T86_19 i) (hfix86_19 i) _)
      ⟨86, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T86_19_2 Q2.hfix86_19_2 Q2.hinj86_19_2
      Q2.hcardT86_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_19_2 i) (Q2.hfix86_19_2 i) _)
      colCert_86_19_5.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T86_19
      hfix86_19 hinj86_19 hcardT86_19
      (fun i => conj_mem_of_fixedPoints _ _ (T86_19 i) (hfix86_19 i) _)
      ⟨86, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T86_19_2 Q2.hfix86_19_2 Q2.hinj86_19_2
      Q2.hcardT86_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_19_2 i) (Q2.hfix86_19_2 i) _)
      colCert_86_19_10.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T86_19
      hfix86_19 hinj86_19 hcardT86_19
      (fun i => conj_mem_of_fixedPoints _ _ (T86_19 i) (hfix86_19 i) _)
      ⟨86, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T86_19_2 Q2.hfix86_19_2 Q2.hinj86_19_2
      Q2.hcardT86_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_19_2 i) (Q2.hfix86_19_2 i) _)
      colCert_86_19_15.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T86_19
      hfix86_19 hinj86_19 hcardT86_19
      (fun i => conj_mem_of_fixedPoints _ _ (T86_19 i) (hfix86_19 i) _)
      ⟨86, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T86_19_2 Q2.hfix86_19_2 Q2.hinj86_19_2
      Q2.hcardT86_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_19_2 i) (Q2.hfix86_19_2 i) _)
      colCert_86_19_20.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T86_20
      hfix86_20 hinj86_20 hcardT86_20
      (fun i => conj_mem_of_fixedPoints _ _ (T86_20 i) (hfix86_20 i) _)
      ⟨86, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T86_20_2 Q2.hfix86_20_2 Q2.hinj86_20_2
      Q2.hcardT86_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_20_2 i) (Q2.hfix86_20_2 i) _)
      colCert_86_20_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T86_20
      hfix86_20 hinj86_20 hcardT86_20
      (fun i => conj_mem_of_fixedPoints _ _ (T86_20 i) (hfix86_20 i) _)
      ⟨86, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T86_20_2 Q2.hfix86_20_2 Q2.hinj86_20_2
      Q2.hcardT86_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_20_2 i) (Q2.hfix86_20_2 i) _)
      colCert_86_20_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T86_20
      hfix86_20 hinj86_20 hcardT86_20
      (fun i => conj_mem_of_fixedPoints _ _ (T86_20 i) (hfix86_20 i) _)
      ⟨86, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T86_20_2 Q2.hfix86_20_2 Q2.hinj86_20_2
      Q2.hcardT86_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_20_2 i) (Q2.hfix86_20_2 i) _)
      colCert_86_20_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T86_20
      hfix86_20 hinj86_20 hcardT86_20
      (fun i => conj_mem_of_fixedPoints _ _ (T86_20 i) (hfix86_20 i) _)
      ⟨86, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T86_20_2 Q2.hfix86_20_2 Q2.hinj86_20_2
      Q2.hcardT86_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_20_2 i) (Q2.hfix86_20_2 i) _)
      colCert_86_20_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T86_20
      hfix86_20 hinj86_20 hcardT86_20
      (fun i => conj_mem_of_fixedPoints _ _ (T86_20 i) (hfix86_20 i) _)
      ⟨86, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T86_20_2 Q2.hfix86_20_2 Q2.hinj86_20_2
      Q2.hcardT86_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_20_2 i) (Q2.hfix86_20_2 i) _)
      colCert_86_20_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T86_20
      hfix86_20 hinj86_20 hcardT86_20
      (fun i => conj_mem_of_fixedPoints _ _ (T86_20 i) (hfix86_20 i) _)
      ⟨86, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T86_20_2 Q2.hfix86_20_2 Q2.hinj86_20_2
      Q2.hcardT86_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_20_2 i) (Q2.hfix86_20_2 i) _)
      colCert_86_20_5.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T86_20
      hfix86_20 hinj86_20 hcardT86_20
      (fun i => conj_mem_of_fixedPoints _ _ (T86_20 i) (hfix86_20 i) _)
      ⟨86, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T86_20_2 Q2.hfix86_20_2 Q2.hinj86_20_2
      Q2.hcardT86_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_20_2 i) (Q2.hfix86_20_2 i) _)
      colCert_86_20_10.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T86_20
      hfix86_20 hinj86_20 hcardT86_20
      (fun i => conj_mem_of_fixedPoints _ _ (T86_20 i) (hfix86_20 i) _)
      ⟨86, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T86_20_2 Q2.hfix86_20_2 Q2.hinj86_20_2
      Q2.hcardT86_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_20_2 i) (Q2.hfix86_20_2 i) _)
      colCert_86_20_15.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T86_20
      hfix86_20 hinj86_20 hcardT86_20
      (fun i => conj_mem_of_fixedPoints _ _ (T86_20 i) (hfix86_20 i) _)
      ⟨86, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T86_20_2 Q2.hfix86_20_2 Q2.hinj86_20_2
      Q2.hcardT86_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_20_2 i) (Q2.hfix86_20_2 i) _)
      colCert_86_20_20.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T86_21
      hfix86_21 hinj86_21 hcardT86_21
      (fun i => conj_mem_of_fixedPoints _ _ (T86_21 i) (hfix86_21 i) _)
      ⟨86, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T86_21_2 Q2.hfix86_21_2 Q2.hinj86_21_2
      Q2.hcardT86_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_21_2 i) (Q2.hfix86_21_2 i) _)
      colCert_86_21_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T86_21
      hfix86_21 hinj86_21 hcardT86_21
      (fun i => conj_mem_of_fixedPoints _ _ (T86_21 i) (hfix86_21 i) _)
      ⟨86, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T86_21_2 Q2.hfix86_21_2 Q2.hinj86_21_2
      Q2.hcardT86_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_21_2 i) (Q2.hfix86_21_2 i) _)
      colCert_86_21_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T86_21
      hfix86_21 hinj86_21 hcardT86_21
      (fun i => conj_mem_of_fixedPoints _ _ (T86_21 i) (hfix86_21 i) _)
      ⟨86, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T86_21_2 Q2.hfix86_21_2 Q2.hinj86_21_2
      Q2.hcardT86_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_21_2 i) (Q2.hfix86_21_2 i) _)
      colCert_86_21_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T86_21
      hfix86_21 hinj86_21 hcardT86_21
      (fun i => conj_mem_of_fixedPoints _ _ (T86_21 i) (hfix86_21 i) _)
      ⟨86, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T86_21_2 Q2.hfix86_21_2 Q2.hinj86_21_2
      Q2.hcardT86_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_21_2 i) (Q2.hfix86_21_2 i) _)
      colCert_86_21_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T86_21
      hfix86_21 hinj86_21 hcardT86_21
      (fun i => conj_mem_of_fixedPoints _ _ (T86_21 i) (hfix86_21 i) _)
      ⟨86, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T86_21_2 Q2.hfix86_21_2 Q2.hinj86_21_2
      Q2.hcardT86_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_21_2 i) (Q2.hfix86_21_2 i) _)
      colCert_86_21_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T86_21
      hfix86_21 hinj86_21 hcardT86_21
      (fun i => conj_mem_of_fixedPoints _ _ (T86_21 i) (hfix86_21 i) _)
      ⟨86, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T86_21_2 Q2.hfix86_21_2 Q2.hinj86_21_2
      Q2.hcardT86_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_21_2 i) (Q2.hfix86_21_2 i) _)
      colCert_86_21_5.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T86_21
      hfix86_21 hinj86_21 hcardT86_21
      (fun i => conj_mem_of_fixedPoints _ _ (T86_21 i) (hfix86_21 i) _)
      ⟨86, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T86_21_2 Q2.hfix86_21_2 Q2.hinj86_21_2
      Q2.hcardT86_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_21_2 i) (Q2.hfix86_21_2 i) _)
      colCert_86_21_10.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T86_21
      hfix86_21 hinj86_21 hcardT86_21
      (fun i => conj_mem_of_fixedPoints _ _ (T86_21 i) (hfix86_21 i) _)
      ⟨86, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T86_21_2 Q2.hfix86_21_2 Q2.hinj86_21_2
      Q2.hcardT86_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_21_2 i) (Q2.hfix86_21_2 i) _)
      colCert_86_21_15.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T86_21
      hfix86_21 hinj86_21 hcardT86_21
      (fun i => conj_mem_of_fixedPoints _ _ (T86_21 i) (hfix86_21 i) _)
      ⟨86, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T86_21_2 Q2.hfix86_21_2 Q2.hinj86_21_2
      Q2.hcardT86_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_21_2 i) (Q2.hfix86_21_2 i) _)
      colCert_86_21_20.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T86_22
      hfix86_22 hinj86_22 hcardT86_22
      (fun i => conj_mem_of_fixedPoints _ _ (T86_22 i) (hfix86_22 i) _)
      ⟨86, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T86_22_2 Q2.hfix86_22_2 Q2.hinj86_22_2
      Q2.hcardT86_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_22_2 i) (Q2.hfix86_22_2 i) _)
      colCert_86_22_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T86_22
      hfix86_22 hinj86_22 hcardT86_22
      (fun i => conj_mem_of_fixedPoints _ _ (T86_22 i) (hfix86_22 i) _)
      ⟨86, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T86_22_2 Q2.hfix86_22_2 Q2.hinj86_22_2
      Q2.hcardT86_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_22_2 i) (Q2.hfix86_22_2 i) _)
      colCert_86_22_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T86_22
      hfix86_22 hinj86_22 hcardT86_22
      (fun i => conj_mem_of_fixedPoints _ _ (T86_22 i) (hfix86_22 i) _)
      ⟨86, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T86_22_2 Q2.hfix86_22_2 Q2.hinj86_22_2
      Q2.hcardT86_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_22_2 i) (Q2.hfix86_22_2 i) _)
      colCert_86_22_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T86_22
      hfix86_22 hinj86_22 hcardT86_22
      (fun i => conj_mem_of_fixedPoints _ _ (T86_22 i) (hfix86_22 i) _)
      ⟨86, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T86_22_2 Q2.hfix86_22_2 Q2.hinj86_22_2
      Q2.hcardT86_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_22_2 i) (Q2.hfix86_22_2 i) _)
      colCert_86_22_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T86_22
      hfix86_22 hinj86_22 hcardT86_22
      (fun i => conj_mem_of_fixedPoints _ _ (T86_22 i) (hfix86_22 i) _)
      ⟨86, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T86_22_2 Q2.hfix86_22_2 Q2.hinj86_22_2
      Q2.hcardT86_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_22_2 i) (Q2.hfix86_22_2 i) _)
      colCert_86_22_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T86_22
      hfix86_22 hinj86_22 hcardT86_22
      (fun i => conj_mem_of_fixedPoints _ _ (T86_22 i) (hfix86_22 i) _)
      ⟨86, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T86_22_2 Q2.hfix86_22_2 Q2.hinj86_22_2
      Q2.hcardT86_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_22_2 i) (Q2.hfix86_22_2 i) _)
      colCert_86_22_5.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T86_22
      hfix86_22 hinj86_22 hcardT86_22
      (fun i => conj_mem_of_fixedPoints _ _ (T86_22 i) (hfix86_22 i) _)
      ⟨86, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T86_22_2 Q2.hfix86_22_2 Q2.hinj86_22_2
      Q2.hcardT86_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_22_2 i) (Q2.hfix86_22_2 i) _)
      colCert_86_22_10.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T86_22
      hfix86_22 hinj86_22 hcardT86_22
      (fun i => conj_mem_of_fixedPoints _ _ (T86_22 i) (hfix86_22 i) _)
      ⟨86, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T86_22_2 Q2.hfix86_22_2 Q2.hinj86_22_2
      Q2.hcardT86_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_22_2 i) (Q2.hfix86_22_2 i) _)
      colCert_86_22_15.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T86_22
      hfix86_22 hinj86_22 hcardT86_22
      (fun i => conj_mem_of_fixedPoints _ _ (T86_22 i) (hfix86_22 i) _)
      ⟨86, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T86_22_2 Q2.hfix86_22_2 Q2.hinj86_22_2
      Q2.hcardT86_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_22_2 i) (Q2.hfix86_22_2 i) _)
      colCert_86_22_20.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T86_23
      hfix86_23 hinj86_23 hcardT86_23
      (fun i => conj_mem_of_fixedPoints _ _ (T86_23 i) (hfix86_23 i) _)
      ⟨86, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T86_23_2 Q2.hfix86_23_2 Q2.hinj86_23_2
      Q2.hcardT86_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_23_2 i) (Q2.hfix86_23_2 i) _)
      colCert_86_23_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T86_23
      hfix86_23 hinj86_23 hcardT86_23
      (fun i => conj_mem_of_fixedPoints _ _ (T86_23 i) (hfix86_23 i) _)
      ⟨86, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T86_23_2 Q2.hfix86_23_2 Q2.hinj86_23_2
      Q2.hcardT86_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_23_2 i) (Q2.hfix86_23_2 i) _)
      colCert_86_23_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T86_23
      hfix86_23 hinj86_23 hcardT86_23
      (fun i => conj_mem_of_fixedPoints _ _ (T86_23 i) (hfix86_23 i) _)
      ⟨86, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T86_23_2 Q2.hfix86_23_2 Q2.hinj86_23_2
      Q2.hcardT86_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_23_2 i) (Q2.hfix86_23_2 i) _)
      colCert_86_23_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T86_23
      hfix86_23 hinj86_23 hcardT86_23
      (fun i => conj_mem_of_fixedPoints _ _ (T86_23 i) (hfix86_23 i) _)
      ⟨86, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T86_23_2 Q2.hfix86_23_2 Q2.hinj86_23_2
      Q2.hcardT86_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_23_2 i) (Q2.hfix86_23_2 i) _)
      colCert_86_23_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T86_23
      hfix86_23 hinj86_23 hcardT86_23
      (fun i => conj_mem_of_fixedPoints _ _ (T86_23 i) (hfix86_23 i) _)
      ⟨86, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T86_23_2 Q2.hfix86_23_2 Q2.hinj86_23_2
      Q2.hcardT86_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_23_2 i) (Q2.hfix86_23_2 i) _)
      colCert_86_23_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T86_23
      hfix86_23 hinj86_23 hcardT86_23
      (fun i => conj_mem_of_fixedPoints _ _ (T86_23 i) (hfix86_23 i) _)
      ⟨86, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T86_23_2 Q2.hfix86_23_2 Q2.hinj86_23_2
      Q2.hcardT86_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_23_2 i) (Q2.hfix86_23_2 i) _)
      colCert_86_23_5.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T86_23
      hfix86_23 hinj86_23 hcardT86_23
      (fun i => conj_mem_of_fixedPoints _ _ (T86_23 i) (hfix86_23 i) _)
      ⟨86, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T86_23_2 Q2.hfix86_23_2 Q2.hinj86_23_2
      Q2.hcardT86_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_23_2 i) (Q2.hfix86_23_2 i) _)
      colCert_86_23_10.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T86_23
      hfix86_23 hinj86_23 hcardT86_23
      (fun i => conj_mem_of_fixedPoints _ _ (T86_23 i) (hfix86_23 i) _)
      ⟨86, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T86_23_2 Q2.hfix86_23_2 Q2.hinj86_23_2
      Q2.hcardT86_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_23_2 i) (Q2.hfix86_23_2 i) _)
      colCert_86_23_15.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T86_23
      hfix86_23 hinj86_23 hcardT86_23
      (fun i => conj_mem_of_fixedPoints _ _ (T86_23 i) (hfix86_23 i) _)
      ⟨86, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T86_23_2 Q2.hfix86_23_2 Q2.hinj86_23_2
      Q2.hcardT86_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_23_2 i) (Q2.hfix86_23_2 i) _)
      colCert_86_23_20.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T86_54
      hfix86_54 hinj86_54 hcardT86_54
      (fun i => conj_mem_of_fixedPoints _ _ (T86_54 i) (hfix86_54 i) _)
      ⟨86, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T86_54_2 Q2.hfix86_54_2 Q2.hinj86_54_2
      Q2.hcardT86_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_54_2 i) (Q2.hfix86_54_2 i) _)
      colCert_86_54_0.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T86_54
      hfix86_54 hinj86_54 hcardT86_54
      (fun i => conj_mem_of_fixedPoints _ _ (T86_54 i) (hfix86_54 i) _)
      ⟨86, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T86_54_2 Q2.hfix86_54_2 Q2.hinj86_54_2
      Q2.hcardT86_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_54_2 i) (Q2.hfix86_54_2 i) _)
      colCert_86_54_1.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T86_54
      hfix86_54 hinj86_54 hcardT86_54
      (fun i => conj_mem_of_fixedPoints _ _ (T86_54 i) (hfix86_54 i) _)
      ⟨86, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T86_54_2 Q2.hfix86_54_2 Q2.hinj86_54_2
      Q2.hcardT86_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_54_2 i) (Q2.hfix86_54_2 i) _)
      colCert_86_54_2.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T86_54
      hfix86_54 hinj86_54 hcardT86_54
      (fun i => conj_mem_of_fixedPoints _ _ (T86_54 i) (hfix86_54 i) _)
      ⟨86, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T86_54_2 Q2.hfix86_54_2 Q2.hinj86_54_2
      Q2.hcardT86_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_54_2 i) (Q2.hfix86_54_2 i) _)
      colCert_86_54_3.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T86_54
      hfix86_54 hinj86_54 hcardT86_54
      (fun i => conj_mem_of_fixedPoints _ _ (T86_54 i) (hfix86_54 i) _)
      ⟨86, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T86_54_2 Q2.hfix86_54_2 Q2.hinj86_54_2
      Q2.hcardT86_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_54_2 i) (Q2.hfix86_54_2 i) _)
      colCert_86_54_4.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T86_54
      hfix86_54 hinj86_54 hcardT86_54
      (fun i => conj_mem_of_fixedPoints _ _ (T86_54 i) (hfix86_54 i) _)
      ⟨86, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T86_54_2 Q2.hfix86_54_2 Q2.hinj86_54_2
      Q2.hcardT86_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_54_2 i) (Q2.hfix86_54_2 i) _)
      colCert_86_54_5.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T86_54
      hfix86_54 hinj86_54 hcardT86_54
      (fun i => conj_mem_of_fixedPoints _ _ (T86_54 i) (hfix86_54 i) _)
      ⟨86, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T86_54_2 Q2.hfix86_54_2 Q2.hinj86_54_2
      Q2.hcardT86_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_54_2 i) (Q2.hfix86_54_2 i) _)
      colCert_86_54_10.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T86_54
      hfix86_54 hinj86_54 hcardT86_54
      (fun i => conj_mem_of_fixedPoints _ _ (T86_54 i) (hfix86_54 i) _)
      ⟨86, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T86_54_2 Q2.hfix86_54_2 Q2.hinj86_54_2
      Q2.hcardT86_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_54_2 i) (Q2.hfix86_54_2 i) _)
      colCert_86_54_15.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T86_54
      hfix86_54 hinj86_54 hcardT86_54
      (fun i => conj_mem_of_fixedPoints _ _ (T86_54 i) (hfix86_54 i) _)
      ⟨86, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T86_54_2 Q2.hfix86_54_2 Q2.hinj86_54_2
      Q2.hcardT86_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_54_2 i) (Q2.hfix86_54_2 i) _)
      colCert_86_54_20.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_0 (hp : 0 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 0 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 0 (transLenTr ⟨86, by decide⟩ 0 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 0 (transLenTr ⟨86, by decide⟩ 0 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 0 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨86, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 0 (transLenTr ⟨86, by decide⟩ 0 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T86_86 = colFn colCertDiv_86_86_0.D1 (m := 5) from colCertDiv_86_86_0.bind1,
    show colData2 (⟨86, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 0 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T86_86_2 = colFn colCertDiv_86_86_0.D2 (m := 5) from colCertDiv_86_86_0.bind2]
  rw [alnId_86 j hj]
  exact fastcode_of_tau ⟨86, by decide⟩ _ _ _
    ((alnId_86 j hj) ▸ Q2.listedAt (⟨86, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨86, by decide⟩ : Fin 148) hj hq).1) colCertDiv_86_86_0_tau_match


theorem leaf_86_86_1 (hp : 1 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 1 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 1 (transLenTr ⟨86, by decide⟩ 1 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 1 (transLenTr ⟨86, by decide⟩ 1 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 1 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨86, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 1 (transLenTr ⟨86, by decide⟩ 1 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T86_86 = colFn colCertDiv_86_86_1.D1 (m := 5) from colCertDiv_86_86_1.bind1,
    show colData2 (⟨86, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 1 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T86_86_2 = colFn colCertDiv_86_86_1.D2 (m := 5) from colCertDiv_86_86_1.bind2]
  rw [alnId_86 j hj]
  exact fastcode_of_tau ⟨86, by decide⟩ _ _ _
    ((alnId_86 j hj) ▸ Q2.listedAt (⟨86, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨86, by decide⟩ : Fin 148) hj hq).1) colCertDiv_86_86_1_tau_match


theorem leaf_86_86_2 (hp : 2 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 2 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 2 (transLenTr ⟨86, by decide⟩ 2 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 2 (transLenTr ⟨86, by decide⟩ 2 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 2 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨86, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 2 (transLenTr ⟨86, by decide⟩ 2 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T86_86 = colFn colCertDiv_86_86_2.D1 (m := 5) from colCertDiv_86_86_2.bind1,
    show colData2 (⟨86, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 2 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T86_86_2 = colFn colCertDiv_86_86_2.D2 (m := 5) from colCertDiv_86_86_2.bind2]
  rw [alnId_86 j hj]
  exact fastcode_of_tau ⟨86, by decide⟩ _ _ _
    ((alnId_86 j hj) ▸ Q2.listedAt (⟨86, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨86, by decide⟩ : Fin 148) hj hq).1) colCertDiv_86_86_2_tau_match


theorem leaf_86_86_3 (hp : 3 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 3 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 3 (transLenTr ⟨86, by decide⟩ 3 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 3 (transLenTr ⟨86, by decide⟩ 3 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 3 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨86, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 3 (transLenTr ⟨86, by decide⟩ 3 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T86_86 = colFn colCertDiv_86_86_3.D1 (m := 5) from colCertDiv_86_86_3.bind1,
    show colData2 (⟨86, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 3 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T86_86_2 = colFn colCertDiv_86_86_3.D2 (m := 5) from colCertDiv_86_86_3.bind2]
  rw [alnId_86 j hj]
  exact fastcode_of_tau ⟨86, by decide⟩ _ _ _
    ((alnId_86 j hj) ▸ Q2.listedAt (⟨86, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨86, by decide⟩ : Fin 148) hj hq).1) colCertDiv_86_86_3_tau_match


theorem leaf_86_86_4 (hp : 4 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 4 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 4 (transLenTr ⟨86, by decide⟩ 4 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 4 (transLenTr ⟨86, by decide⟩ 4 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 4 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      ?_).symm
  rw [show colData1 (⟨86, by decide⟩ : Fin 148)
        ((colE1 ⟨86, by decide⟩ 4 (transLenTr ⟨86, by decide⟩ 4 hp) : ↥(reps ⟨86, by decide⟩)) : Coordinate 1)
        T86_86 = colFn colCertDiv_86_86_4.D1 (m := 5) from colCertDiv_86_86_4.bind1,
    show colData2 (⟨86, by decide⟩ : Fin 148)
        ((colE2 ⟨86, by decide⟩ 4 hp : ↥(Q2.reps ⟨86, by decide⟩)) : Coordinate 2)
        Q2.T86_86_2 = colFn colCertDiv_86_86_4.D2 (m := 5) from colCertDiv_86_86_4.bind2]
  rw [alnId_86 j hj]
  exact fastcode_of_tau ⟨86, by decide⟩ _ _ _
    ((alnId_86 j hj) ▸ Q2.listedAt (⟨86, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨86, by decide⟩ : Fin 148) hj hq).1) colCertDiv_86_86_4_tau_match


theorem leaf_86_86_5 (hp : 5 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 5 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 5 (transLenTr ⟨86, by decide⟩ 5 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 5 (transLenTr ⟨86, by decide⟩ 5 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 5 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_5.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_6 (hp : 6 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 6 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 6 (transLenTr ⟨86, by decide⟩ 6 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 6 (transLenTr ⟨86, by decide⟩ 6 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 6 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_6.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_7 (hp : 7 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 7 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 7 (transLenTr ⟨86, by decide⟩ 7 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 7 (transLenTr ⟨86, by decide⟩ 7 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 7 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_7.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_8 (hp : 8 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 8 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 8 (transLenTr ⟨86, by decide⟩ 8 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 8 (transLenTr ⟨86, by decide⟩ 8 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 8 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_8.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_9 (hp : 9 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 9 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 9 (transLenTr ⟨86, by decide⟩ 9 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 9 (transLenTr ⟨86, by decide⟩ 9 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 9 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_9.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_10 (hp : 10 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 10 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 10 (transLenTr ⟨86, by decide⟩ 10 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 10 (transLenTr ⟨86, by decide⟩ 10 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 10 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_10.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_11 (hp : 11 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 11 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 11 (transLenTr ⟨86, by decide⟩ 11 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 11 (transLenTr ⟨86, by decide⟩ 11 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 11 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_11.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_12 (hp : 12 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 12 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 12 (transLenTr ⟨86, by decide⟩ 12 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 12 (transLenTr ⟨86, by decide⟩ 12 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 12 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_12.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_13 (hp : 13 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 13 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 13 (transLenTr ⟨86, by decide⟩ 13 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 13 (transLenTr ⟨86, by decide⟩ 13 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 13 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_13.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_14 (hp : 14 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 14 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 14 (transLenTr ⟨86, by decide⟩ 14 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 14 (transLenTr ⟨86, by decide⟩ 14 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 14 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_14.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_15 (hp : 15 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 15 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 15 (transLenTr ⟨86, by decide⟩ 15 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 15 (transLenTr ⟨86, by decide⟩ 15 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 15 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_15.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_16 (hp : 16 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 16 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 16 (transLenTr ⟨86, by decide⟩ 16 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 16 (transLenTr ⟨86, by decide⟩ 16 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 16 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_16.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_17 (hp : 17 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 17 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 17 (transLenTr ⟨86, by decide⟩ 17 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 17 (transLenTr ⟨86, by decide⟩ 17 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 17 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_17.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_18 (hp : 18 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 18 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 18 (transLenTr ⟨86, by decide⟩ 18 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 18 (transLenTr ⟨86, by decide⟩ 18 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 18 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_18.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_19 (hp : 19 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 19 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 19 (transLenTr ⟨86, by decide⟩ 19 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 19 (transLenTr ⟨86, by decide⟩ 19 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 19 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_19.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_20 (hp : 20 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 20 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 20 (transLenTr ⟨86, by decide⟩ 20 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 20 (transLenTr ⟨86, by decide⟩ 20 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 20 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_20.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_21 (hp : 21 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 21 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 21 (transLenTr ⟨86, by decide⟩ 21 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 21 (transLenTr ⟨86, by decide⟩ 21 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 21 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_21.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_22 (hp : 22 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 22 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 22 (transLenTr ⟨86, by decide⟩ 22 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 22 (transLenTr ⟨86, by decide⟩ 22 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 22 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_22.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_23 (hp : 23 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 23 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 23 (transLenTr ⟨86, by decide⟩ 23 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 23 (transLenTr ⟨86, by decide⟩ 23 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 23 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_23.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_86_86_24 (hp : 24 < (Q2.transData.getD 86 []).length)
    (j : Nat) (hj : j < (repChars.getD 86 []).length)
    (hq : (normIsRep.getD 86 []).getD j false = true) :
    species (Q2.reps (⟨86, by decide⟩ : Fin 148)) (colE2 ⟨86, by decide⟩ 24 hp)
        (rowE2 (⟨86, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨86, by decide⟩ : Fin 148))
        (colE1 ⟨86, by decide⟩ 24 (transLenTr ⟨86, by decide⟩ 24 hp))
        (rowE1 (⟨86, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨86, by decide⟩ : Fin 148) ⟨86, by decide⟩ _
      (validAt ⟨86, by decide⟩ (listedAt ⟨86, by decide⟩ hj))
      (colE1 ⟨86, by decide⟩ 24 (transLenTr ⟨86, by decide⟩ 24 hp)) T86_86
      hfix86_86 hinj86_86 hcardT86_86
      (fun i => conj_mem_of_fixedPoints _ _ (T86_86 i) (hfix86_86 i) _)
      ⟨86, by decide⟩ ⟨86, by decide⟩ _
      (Q2.validAt ⟨86, by decide⟩ (Q2.listedAt ⟨86, by decide⟩
        (alnCheck_rep ⟨86, by decide⟩ hj hq).1))
      (colE2 ⟨86, by decide⟩ 24 hp) Q2.T86_86_2 Q2.hfix86_86_2 Q2.hinj86_86_2
      Q2.hcardT86_86_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T86_86_2 i) (Q2.hfix86_86_2 i) _)
      colCert_86_86_24.hD ?_).symm
  rw [alnId_86 j hj]


theorem leaf_87_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T87_2
      hfix87_2 hinj87_2 hcardT87_2
      (fun i => conj_mem_of_fixedPoints _ _ (T87_2 i) (hfix87_2 i) _)
      ⟨87, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T87_2_2 Q2.hfix87_2_2 Q2.hinj87_2_2
      Q2.hcardT87_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_2_2 i) (Q2.hfix87_2_2 i) _)
      colCert_87_2_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T87_2
      hfix87_2 hinj87_2 hcardT87_2
      (fun i => conj_mem_of_fixedPoints _ _ (T87_2 i) (hfix87_2 i) _)
      ⟨87, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T87_2_2 Q2.hfix87_2_2 Q2.hinj87_2_2
      Q2.hcardT87_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_2_2 i) (Q2.hfix87_2_2 i) _)
      colCert_87_2_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T87_2
      hfix87_2 hinj87_2 hcardT87_2
      (fun i => conj_mem_of_fixedPoints _ _ (T87_2 i) (hfix87_2 i) _)
      ⟨87, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T87_2_2 Q2.hfix87_2_2 Q2.hinj87_2_2
      Q2.hcardT87_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_2_2 i) (Q2.hfix87_2_2 i) _)
      colCert_87_2_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T87_2
      hfix87_2 hinj87_2 hcardT87_2
      (fun i => conj_mem_of_fixedPoints _ _ (T87_2 i) (hfix87_2 i) _)
      ⟨87, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T87_2_2 Q2.hfix87_2_2 Q2.hinj87_2_2
      Q2.hcardT87_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_2_2 i) (Q2.hfix87_2_2 i) _)
      colCert_87_2_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T87_2
      hfix87_2 hinj87_2 hcardT87_2
      (fun i => conj_mem_of_fixedPoints _ _ (T87_2 i) (hfix87_2 i) _)
      ⟨87, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T87_2_2 Q2.hfix87_2_2 Q2.hinj87_2_2
      Q2.hcardT87_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_2_2 i) (Q2.hfix87_2_2 i) _)
      colCert_87_2_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T87_3
      hfix87_3 hinj87_3 hcardT87_3
      (fun i => conj_mem_of_fixedPoints _ _ (T87_3 i) (hfix87_3 i) _)
      ⟨87, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T87_3_2 Q2.hfix87_3_2 Q2.hinj87_3_2
      Q2.hcardT87_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_3_2 i) (Q2.hfix87_3_2 i) _)
      colCert_87_3_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T87_3
      hfix87_3 hinj87_3 hcardT87_3
      (fun i => conj_mem_of_fixedPoints _ _ (T87_3 i) (hfix87_3 i) _)
      ⟨87, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T87_3_2 Q2.hfix87_3_2 Q2.hinj87_3_2
      Q2.hcardT87_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_3_2 i) (Q2.hfix87_3_2 i) _)
      colCert_87_3_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T87_3
      hfix87_3 hinj87_3 hcardT87_3
      (fun i => conj_mem_of_fixedPoints _ _ (T87_3 i) (hfix87_3 i) _)
      ⟨87, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T87_3_2 Q2.hfix87_3_2 Q2.hinj87_3_2
      Q2.hcardT87_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_3_2 i) (Q2.hfix87_3_2 i) _)
      colCert_87_3_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T87_3
      hfix87_3 hinj87_3 hcardT87_3
      (fun i => conj_mem_of_fixedPoints _ _ (T87_3 i) (hfix87_3 i) _)
      ⟨87, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T87_3_2 Q2.hfix87_3_2 Q2.hinj87_3_2
      Q2.hcardT87_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_3_2 i) (Q2.hfix87_3_2 i) _)
      colCert_87_3_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T87_3
      hfix87_3 hinj87_3 hcardT87_3
      (fun i => conj_mem_of_fixedPoints _ _ (T87_3 i) (hfix87_3 i) _)
      ⟨87, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T87_3_2 Q2.hfix87_3_2 Q2.hinj87_3_2
      Q2.hcardT87_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_3_2 i) (Q2.hfix87_3_2 i) _)
      colCert_87_3_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T87_4
      hfix87_4 hinj87_4 hcardT87_4
      (fun i => conj_mem_of_fixedPoints _ _ (T87_4 i) (hfix87_4 i) _)
      ⟨87, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T87_4_2 Q2.hfix87_4_2 Q2.hinj87_4_2
      Q2.hcardT87_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_4_2 i) (Q2.hfix87_4_2 i) _)
      colCert_87_4_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T87_4
      hfix87_4 hinj87_4 hcardT87_4
      (fun i => conj_mem_of_fixedPoints _ _ (T87_4 i) (hfix87_4 i) _)
      ⟨87, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T87_4_2 Q2.hfix87_4_2 Q2.hinj87_4_2
      Q2.hcardT87_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_4_2 i) (Q2.hfix87_4_2 i) _)
      colCert_87_4_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T87_4
      hfix87_4 hinj87_4 hcardT87_4
      (fun i => conj_mem_of_fixedPoints _ _ (T87_4 i) (hfix87_4 i) _)
      ⟨87, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T87_4_2 Q2.hfix87_4_2 Q2.hinj87_4_2
      Q2.hcardT87_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_4_2 i) (Q2.hfix87_4_2 i) _)
      colCert_87_4_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T87_4
      hfix87_4 hinj87_4 hcardT87_4
      (fun i => conj_mem_of_fixedPoints _ _ (T87_4 i) (hfix87_4 i) _)
      ⟨87, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T87_4_2 Q2.hfix87_4_2 Q2.hinj87_4_2
      Q2.hcardT87_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_4_2 i) (Q2.hfix87_4_2 i) _)
      colCert_87_4_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T87_4
      hfix87_4 hinj87_4 hcardT87_4
      (fun i => conj_mem_of_fixedPoints _ _ (T87_4 i) (hfix87_4 i) _)
      ⟨87, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T87_4_2 Q2.hfix87_4_2 Q2.hinj87_4_2
      Q2.hcardT87_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_4_2 i) (Q2.hfix87_4_2 i) _)
      colCert_87_4_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T87_5
      hfix87_5 hinj87_5 hcardT87_5
      (fun i => conj_mem_of_fixedPoints _ _ (T87_5 i) (hfix87_5 i) _)
      ⟨87, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T87_5_2 Q2.hfix87_5_2 Q2.hinj87_5_2
      Q2.hcardT87_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_5_2 i) (Q2.hfix87_5_2 i) _)
      colCert_87_5_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T87_5
      hfix87_5 hinj87_5 hcardT87_5
      (fun i => conj_mem_of_fixedPoints _ _ (T87_5 i) (hfix87_5 i) _)
      ⟨87, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T87_5_2 Q2.hfix87_5_2 Q2.hinj87_5_2
      Q2.hcardT87_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_5_2 i) (Q2.hfix87_5_2 i) _)
      colCert_87_5_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T87_5
      hfix87_5 hinj87_5 hcardT87_5
      (fun i => conj_mem_of_fixedPoints _ _ (T87_5 i) (hfix87_5 i) _)
      ⟨87, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T87_5_2 Q2.hfix87_5_2 Q2.hinj87_5_2
      Q2.hcardT87_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_5_2 i) (Q2.hfix87_5_2 i) _)
      colCert_87_5_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T87_5
      hfix87_5 hinj87_5 hcardT87_5
      (fun i => conj_mem_of_fixedPoints _ _ (T87_5 i) (hfix87_5 i) _)
      ⟨87, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T87_5_2 Q2.hfix87_5_2 Q2.hinj87_5_2
      Q2.hcardT87_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_5_2 i) (Q2.hfix87_5_2 i) _)
      colCert_87_5_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T87_5
      hfix87_5 hinj87_5 hcardT87_5
      (fun i => conj_mem_of_fixedPoints _ _ (T87_5 i) (hfix87_5 i) _)
      ⟨87, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T87_5_2 Q2.hfix87_5_2 Q2.hinj87_5_2
      Q2.hcardT87_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_5_2 i) (Q2.hfix87_5_2 i) _)
      colCert_87_5_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T87_7
      hfix87_7 hinj87_7 hcardT87_7
      (fun i => conj_mem_of_fixedPoints _ _ (T87_7 i) (hfix87_7 i) _)
      ⟨87, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T87_7_2 Q2.hfix87_7_2 Q2.hinj87_7_2
      Q2.hcardT87_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_7_2 i) (Q2.hfix87_7_2 i) _)
      colCert_87_7_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T87_7
      hfix87_7 hinj87_7 hcardT87_7
      (fun i => conj_mem_of_fixedPoints _ _ (T87_7 i) (hfix87_7 i) _)
      ⟨87, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T87_7_2 Q2.hfix87_7_2 Q2.hinj87_7_2
      Q2.hcardT87_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_7_2 i) (Q2.hfix87_7_2 i) _)
      colCert_87_7_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T87_7
      hfix87_7 hinj87_7 hcardT87_7
      (fun i => conj_mem_of_fixedPoints _ _ (T87_7 i) (hfix87_7 i) _)
      ⟨87, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T87_7_2 Q2.hfix87_7_2 Q2.hinj87_7_2
      Q2.hcardT87_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_7_2 i) (Q2.hfix87_7_2 i) _)
      colCert_87_7_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T87_7
      hfix87_7 hinj87_7 hcardT87_7
      (fun i => conj_mem_of_fixedPoints _ _ (T87_7 i) (hfix87_7 i) _)
      ⟨87, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T87_7_2 Q2.hfix87_7_2 Q2.hinj87_7_2
      Q2.hcardT87_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_7_2 i) (Q2.hfix87_7_2 i) _)
      colCert_87_7_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T87_7
      hfix87_7 hinj87_7 hcardT87_7
      (fun i => conj_mem_of_fixedPoints _ _ (T87_7 i) (hfix87_7 i) _)
      ⟨87, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T87_7_2 Q2.hfix87_7_2 Q2.hinj87_7_2
      Q2.hcardT87_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_7_2 i) (Q2.hfix87_7_2 i) _)
      colCert_87_7_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T87_11
      hfix87_11 hinj87_11 hcardT87_11
      (fun i => conj_mem_of_fixedPoints _ _ (T87_11 i) (hfix87_11 i) _)
      ⟨87, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T87_11_2 Q2.hfix87_11_2 Q2.hinj87_11_2
      Q2.hcardT87_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_11_2 i) (Q2.hfix87_11_2 i) _)
      colCert_87_11_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T87_11
      hfix87_11 hinj87_11 hcardT87_11
      (fun i => conj_mem_of_fixedPoints _ _ (T87_11 i) (hfix87_11 i) _)
      ⟨87, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T87_11_2 Q2.hfix87_11_2 Q2.hinj87_11_2
      Q2.hcardT87_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_11_2 i) (Q2.hfix87_11_2 i) _)
      colCert_87_11_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T87_11
      hfix87_11 hinj87_11 hcardT87_11
      (fun i => conj_mem_of_fixedPoints _ _ (T87_11 i) (hfix87_11 i) _)
      ⟨87, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T87_11_2 Q2.hfix87_11_2 Q2.hinj87_11_2
      Q2.hcardT87_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_11_2 i) (Q2.hfix87_11_2 i) _)
      colCert_87_11_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T87_11
      hfix87_11 hinj87_11 hcardT87_11
      (fun i => conj_mem_of_fixedPoints _ _ (T87_11 i) (hfix87_11 i) _)
      ⟨87, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T87_11_2 Q2.hfix87_11_2 Q2.hinj87_11_2
      Q2.hcardT87_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_11_2 i) (Q2.hfix87_11_2 i) _)
      colCert_87_11_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T87_11
      hfix87_11 hinj87_11 hcardT87_11
      (fun i => conj_mem_of_fixedPoints _ _ (T87_11 i) (hfix87_11 i) _)
      ⟨87, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T87_11_2 Q2.hfix87_11_2 Q2.hinj87_11_2
      Q2.hcardT87_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_11_2 i) (Q2.hfix87_11_2 i) _)
      colCert_87_11_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T87_12
      hfix87_12 hinj87_12 hcardT87_12
      (fun i => conj_mem_of_fixedPoints _ _ (T87_12 i) (hfix87_12 i) _)
      ⟨87, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T87_12_2 Q2.hfix87_12_2 Q2.hinj87_12_2
      Q2.hcardT87_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_12_2 i) (Q2.hfix87_12_2 i) _)
      colCert_87_12_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T87_12
      hfix87_12 hinj87_12 hcardT87_12
      (fun i => conj_mem_of_fixedPoints _ _ (T87_12 i) (hfix87_12 i) _)
      ⟨87, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T87_12_2 Q2.hfix87_12_2 Q2.hinj87_12_2
      Q2.hcardT87_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_12_2 i) (Q2.hfix87_12_2 i) _)
      colCert_87_12_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T87_12
      hfix87_12 hinj87_12 hcardT87_12
      (fun i => conj_mem_of_fixedPoints _ _ (T87_12 i) (hfix87_12 i) _)
      ⟨87, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T87_12_2 Q2.hfix87_12_2 Q2.hinj87_12_2
      Q2.hcardT87_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_12_2 i) (Q2.hfix87_12_2 i) _)
      colCert_87_12_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T87_12
      hfix87_12 hinj87_12 hcardT87_12
      (fun i => conj_mem_of_fixedPoints _ _ (T87_12 i) (hfix87_12 i) _)
      ⟨87, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T87_12_2 Q2.hfix87_12_2 Q2.hinj87_12_2
      Q2.hcardT87_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_12_2 i) (Q2.hfix87_12_2 i) _)
      colCert_87_12_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T87_12
      hfix87_12 hinj87_12 hcardT87_12
      (fun i => conj_mem_of_fixedPoints _ _ (T87_12 i) (hfix87_12 i) _)
      ⟨87, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T87_12_2 Q2.hfix87_12_2 Q2.hinj87_12_2
      Q2.hcardT87_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_12_2 i) (Q2.hfix87_12_2 i) _)
      colCert_87_12_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T87_20
      hfix87_20 hinj87_20 hcardT87_20
      (fun i => conj_mem_of_fixedPoints _ _ (T87_20 i) (hfix87_20 i) _)
      ⟨87, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T87_20_2 Q2.hfix87_20_2 Q2.hinj87_20_2
      Q2.hcardT87_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_20_2 i) (Q2.hfix87_20_2 i) _)
      colCert_87_20_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T87_20
      hfix87_20 hinj87_20 hcardT87_20
      (fun i => conj_mem_of_fixedPoints _ _ (T87_20 i) (hfix87_20 i) _)
      ⟨87, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T87_20_2 Q2.hfix87_20_2 Q2.hinj87_20_2
      Q2.hcardT87_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_20_2 i) (Q2.hfix87_20_2 i) _)
      colCert_87_20_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T87_20
      hfix87_20 hinj87_20 hcardT87_20
      (fun i => conj_mem_of_fixedPoints _ _ (T87_20 i) (hfix87_20 i) _)
      ⟨87, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T87_20_2 Q2.hfix87_20_2 Q2.hinj87_20_2
      Q2.hcardT87_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_20_2 i) (Q2.hfix87_20_2 i) _)
      colCert_87_20_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T87_20
      hfix87_20 hinj87_20 hcardT87_20
      (fun i => conj_mem_of_fixedPoints _ _ (T87_20 i) (hfix87_20 i) _)
      ⟨87, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T87_20_2 Q2.hfix87_20_2 Q2.hinj87_20_2
      Q2.hcardT87_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_20_2 i) (Q2.hfix87_20_2 i) _)
      colCert_87_20_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T87_20
      hfix87_20 hinj87_20 hcardT87_20
      (fun i => conj_mem_of_fixedPoints _ _ (T87_20 i) (hfix87_20 i) _)
      ⟨87, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T87_20_2 Q2.hfix87_20_2 Q2.hinj87_20_2
      Q2.hcardT87_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_20_2 i) (Q2.hfix87_20_2 i) _)
      colCert_87_20_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T87_20
      hfix87_20 hinj87_20 hcardT87_20
      (fun i => conj_mem_of_fixedPoints _ _ (T87_20 i) (hfix87_20 i) _)
      ⟨87, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T87_20_2 Q2.hfix87_20_2 Q2.hinj87_20_2
      Q2.hcardT87_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_20_2 i) (Q2.hfix87_20_2 i) _)
      colCert_87_20_5.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T87_20
      hfix87_20 hinj87_20 hcardT87_20
      (fun i => conj_mem_of_fixedPoints _ _ (T87_20 i) (hfix87_20 i) _)
      ⟨87, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T87_20_2 Q2.hfix87_20_2 Q2.hinj87_20_2
      Q2.hcardT87_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_20_2 i) (Q2.hfix87_20_2 i) _)
      colCert_87_20_10.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T87_20
      hfix87_20 hinj87_20 hcardT87_20
      (fun i => conj_mem_of_fixedPoints _ _ (T87_20 i) (hfix87_20 i) _)
      ⟨87, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T87_20_2 Q2.hfix87_20_2 Q2.hinj87_20_2
      Q2.hcardT87_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_20_2 i) (Q2.hfix87_20_2 i) _)
      colCert_87_20_15.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T87_20
      hfix87_20 hinj87_20 hcardT87_20
      (fun i => conj_mem_of_fixedPoints _ _ (T87_20 i) (hfix87_20 i) _)
      ⟨87, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T87_20_2 Q2.hfix87_20_2 Q2.hinj87_20_2
      Q2.hcardT87_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_20_2 i) (Q2.hfix87_20_2 i) _)
      colCert_87_20_20.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T87_21
      hfix87_21 hinj87_21 hcardT87_21
      (fun i => conj_mem_of_fixedPoints _ _ (T87_21 i) (hfix87_21 i) _)
      ⟨87, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T87_21_2 Q2.hfix87_21_2 Q2.hinj87_21_2
      Q2.hcardT87_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_21_2 i) (Q2.hfix87_21_2 i) _)
      colCert_87_21_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T87_21
      hfix87_21 hinj87_21 hcardT87_21
      (fun i => conj_mem_of_fixedPoints _ _ (T87_21 i) (hfix87_21 i) _)
      ⟨87, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T87_21_2 Q2.hfix87_21_2 Q2.hinj87_21_2
      Q2.hcardT87_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_21_2 i) (Q2.hfix87_21_2 i) _)
      colCert_87_21_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T87_21
      hfix87_21 hinj87_21 hcardT87_21
      (fun i => conj_mem_of_fixedPoints _ _ (T87_21 i) (hfix87_21 i) _)
      ⟨87, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T87_21_2 Q2.hfix87_21_2 Q2.hinj87_21_2
      Q2.hcardT87_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_21_2 i) (Q2.hfix87_21_2 i) _)
      colCert_87_21_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T87_21
      hfix87_21 hinj87_21 hcardT87_21
      (fun i => conj_mem_of_fixedPoints _ _ (T87_21 i) (hfix87_21 i) _)
      ⟨87, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T87_21_2 Q2.hfix87_21_2 Q2.hinj87_21_2
      Q2.hcardT87_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_21_2 i) (Q2.hfix87_21_2 i) _)
      colCert_87_21_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T87_21
      hfix87_21 hinj87_21 hcardT87_21
      (fun i => conj_mem_of_fixedPoints _ _ (T87_21 i) (hfix87_21 i) _)
      ⟨87, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T87_21_2 Q2.hfix87_21_2 Q2.hinj87_21_2
      Q2.hcardT87_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_21_2 i) (Q2.hfix87_21_2 i) _)
      colCert_87_21_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T87_21
      hfix87_21 hinj87_21 hcardT87_21
      (fun i => conj_mem_of_fixedPoints _ _ (T87_21 i) (hfix87_21 i) _)
      ⟨87, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T87_21_2 Q2.hfix87_21_2 Q2.hinj87_21_2
      Q2.hcardT87_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_21_2 i) (Q2.hfix87_21_2 i) _)
      colCert_87_21_5.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T87_21
      hfix87_21 hinj87_21 hcardT87_21
      (fun i => conj_mem_of_fixedPoints _ _ (T87_21 i) (hfix87_21 i) _)
      ⟨87, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T87_21_2 Q2.hfix87_21_2 Q2.hinj87_21_2
      Q2.hcardT87_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_21_2 i) (Q2.hfix87_21_2 i) _)
      colCert_87_21_10.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T87_21
      hfix87_21 hinj87_21 hcardT87_21
      (fun i => conj_mem_of_fixedPoints _ _ (T87_21 i) (hfix87_21 i) _)
      ⟨87, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T87_21_2 Q2.hfix87_21_2 Q2.hinj87_21_2
      Q2.hcardT87_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_21_2 i) (Q2.hfix87_21_2 i) _)
      colCert_87_21_15.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T87_21
      hfix87_21 hinj87_21 hcardT87_21
      (fun i => conj_mem_of_fixedPoints _ _ (T87_21 i) (hfix87_21 i) _)
      ⟨87, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T87_21_2 Q2.hfix87_21_2 Q2.hinj87_21_2
      Q2.hcardT87_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_21_2 i) (Q2.hfix87_21_2 i) _)
      colCert_87_21_20.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T87_22
      hfix87_22 hinj87_22 hcardT87_22
      (fun i => conj_mem_of_fixedPoints _ _ (T87_22 i) (hfix87_22 i) _)
      ⟨87, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T87_22_2 Q2.hfix87_22_2 Q2.hinj87_22_2
      Q2.hcardT87_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_22_2 i) (Q2.hfix87_22_2 i) _)
      colCert_87_22_0.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T87_22
      hfix87_22 hinj87_22 hcardT87_22
      (fun i => conj_mem_of_fixedPoints _ _ (T87_22 i) (hfix87_22 i) _)
      ⟨87, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T87_22_2 Q2.hfix87_22_2 Q2.hinj87_22_2
      Q2.hcardT87_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_22_2 i) (Q2.hfix87_22_2 i) _)
      colCert_87_22_1.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T87_22
      hfix87_22 hinj87_22 hcardT87_22
      (fun i => conj_mem_of_fixedPoints _ _ (T87_22 i) (hfix87_22 i) _)
      ⟨87, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T87_22_2 Q2.hfix87_22_2 Q2.hinj87_22_2
      Q2.hcardT87_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_22_2 i) (Q2.hfix87_22_2 i) _)
      colCert_87_22_2.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T87_22
      hfix87_22 hinj87_22 hcardT87_22
      (fun i => conj_mem_of_fixedPoints _ _ (T87_22 i) (hfix87_22 i) _)
      ⟨87, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T87_22_2 Q2.hfix87_22_2 Q2.hinj87_22_2
      Q2.hcardT87_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_22_2 i) (Q2.hfix87_22_2 i) _)
      colCert_87_22_3.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T87_22
      hfix87_22 hinj87_22 hcardT87_22
      (fun i => conj_mem_of_fixedPoints _ _ (T87_22 i) (hfix87_22 i) _)
      ⟨87, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T87_22_2 Q2.hfix87_22_2 Q2.hinj87_22_2
      Q2.hcardT87_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_22_2 i) (Q2.hfix87_22_2 i) _)
      colCert_87_22_4.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T87_22
      hfix87_22 hinj87_22 hcardT87_22
      (fun i => conj_mem_of_fixedPoints _ _ (T87_22 i) (hfix87_22 i) _)
      ⟨87, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T87_22_2 Q2.hfix87_22_2 Q2.hinj87_22_2
      Q2.hcardT87_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_22_2 i) (Q2.hfix87_22_2 i) _)
      colCert_87_22_5.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T87_22
      hfix87_22 hinj87_22 hcardT87_22
      (fun i => conj_mem_of_fixedPoints _ _ (T87_22 i) (hfix87_22 i) _)
      ⟨87, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T87_22_2 Q2.hfix87_22_2 Q2.hinj87_22_2
      Q2.hcardT87_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_22_2 i) (Q2.hfix87_22_2 i) _)
      colCert_87_22_10.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T87_22
      hfix87_22 hinj87_22 hcardT87_22
      (fun i => conj_mem_of_fixedPoints _ _ (T87_22 i) (hfix87_22 i) _)
      ⟨87, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T87_22_2 Q2.hfix87_22_2 Q2.hinj87_22_2
      Q2.hcardT87_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_22_2 i) (Q2.hfix87_22_2 i) _)
      colCert_87_22_15.hD ?_).symm
  rw [alnId_87 j hj]


theorem leaf_87_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 87 []).length)
    (hq : (normIsRep.getD 87 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨87, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨87, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨87, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨87, by decide⟩ (listedAt ⟨87, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T87_22
      hfix87_22 hinj87_22 hcardT87_22
      (fun i => conj_mem_of_fixedPoints _ _ (T87_22 i) (hfix87_22 i) _)
      ⟨87, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨87, by decide⟩ (Q2.listedAt ⟨87, by decide⟩
        (alnCheck_rep ⟨87, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T87_22_2 Q2.hfix87_22_2 Q2.hinj87_22_2
      Q2.hcardT87_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T87_22_2 i) (Q2.hfix87_22_2 i) _)
      colCert_87_22_20.hD ?_).symm
  rw [alnId_87 j hj]


end LeanDring.P5Presentation
