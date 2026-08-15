/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C178
import LeanDring.P5.Data.ColRestCheap.C179
import LeanDring.P5.Data.ColRestCheap.C180
import LeanDring.P5.Data.ColRestCheap.C181
import LeanDring.P5.Data.ColRestCheap.C182
import LeanDring.P5.Data.EntryK.C019
import LeanDring.P5.Data.EntryK.C020
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore

/-! # Stage-5 leaves, chunk 14 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_83_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T83_22
      hfix83_22 hinj83_22 hcardT83_22
      (fun i => conj_mem_of_fixedPoints _ _ (T83_22 i) (hfix83_22 i) _)
      ⟨83, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T83_22_2 Q2.hfix83_22_2 Q2.hinj83_22_2
      Q2.hcardT83_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_22_2 i) (Q2.hfix83_22_2 i) _)
      colCert_83_22_4.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T83_22
      hfix83_22 hinj83_22 hcardT83_22
      (fun i => conj_mem_of_fixedPoints _ _ (T83_22 i) (hfix83_22 i) _)
      ⟨83, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T83_22_2 Q2.hfix83_22_2 Q2.hinj83_22_2
      Q2.hcardT83_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_22_2 i) (Q2.hfix83_22_2 i) _)
      colCert_83_22_5.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T83_22
      hfix83_22 hinj83_22 hcardT83_22
      (fun i => conj_mem_of_fixedPoints _ _ (T83_22 i) (hfix83_22 i) _)
      ⟨83, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T83_22_2 Q2.hfix83_22_2 Q2.hinj83_22_2
      Q2.hcardT83_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_22_2 i) (Q2.hfix83_22_2 i) _)
      colCert_83_22_10.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T83_22
      hfix83_22 hinj83_22 hcardT83_22
      (fun i => conj_mem_of_fixedPoints _ _ (T83_22 i) (hfix83_22 i) _)
      ⟨83, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T83_22_2 Q2.hfix83_22_2 Q2.hinj83_22_2
      Q2.hcardT83_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_22_2 i) (Q2.hfix83_22_2 i) _)
      colCert_83_22_15.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T83_22
      hfix83_22 hinj83_22 hcardT83_22
      (fun i => conj_mem_of_fixedPoints _ _ (T83_22 i) (hfix83_22 i) _)
      ⟨83, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T83_22_2 Q2.hfix83_22_2 Q2.hinj83_22_2
      Q2.hcardT83_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_22_2 i) (Q2.hfix83_22_2 i) _)
      colCert_83_22_20.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T83_53
      hfix83_53 hinj83_53 hcardT83_53
      (fun i => conj_mem_of_fixedPoints _ _ (T83_53 i) (hfix83_53 i) _)
      ⟨83, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T83_53_2 Q2.hfix83_53_2 Q2.hinj83_53_2
      Q2.hcardT83_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_53_2 i) (Q2.hfix83_53_2 i) _)
      colCert_83_53_0.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T83_53
      hfix83_53 hinj83_53 hcardT83_53
      (fun i => conj_mem_of_fixedPoints _ _ (T83_53 i) (hfix83_53 i) _)
      ⟨83, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T83_53_2 Q2.hfix83_53_2 Q2.hinj83_53_2
      Q2.hcardT83_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_53_2 i) (Q2.hfix83_53_2 i) _)
      colCert_83_53_1.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T83_53
      hfix83_53 hinj83_53 hcardT83_53
      (fun i => conj_mem_of_fixedPoints _ _ (T83_53 i) (hfix83_53 i) _)
      ⟨83, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T83_53_2 Q2.hfix83_53_2 Q2.hinj83_53_2
      Q2.hcardT83_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_53_2 i) (Q2.hfix83_53_2 i) _)
      colCert_83_53_2.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T83_53
      hfix83_53 hinj83_53 hcardT83_53
      (fun i => conj_mem_of_fixedPoints _ _ (T83_53 i) (hfix83_53 i) _)
      ⟨83, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T83_53_2 Q2.hfix83_53_2 Q2.hinj83_53_2
      Q2.hcardT83_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_53_2 i) (Q2.hfix83_53_2 i) _)
      colCert_83_53_3.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T83_53
      hfix83_53 hinj83_53 hcardT83_53
      (fun i => conj_mem_of_fixedPoints _ _ (T83_53 i) (hfix83_53 i) _)
      ⟨83, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T83_53_2 Q2.hfix83_53_2 Q2.hinj83_53_2
      Q2.hcardT83_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_53_2 i) (Q2.hfix83_53_2 i) _)
      colCert_83_53_4.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T83_53
      hfix83_53 hinj83_53 hcardT83_53
      (fun i => conj_mem_of_fixedPoints _ _ (T83_53 i) (hfix83_53 i) _)
      ⟨83, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T83_53_2 Q2.hfix83_53_2 Q2.hinj83_53_2
      Q2.hcardT83_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_53_2 i) (Q2.hfix83_53_2 i) _)
      colCert_83_53_5.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T83_53
      hfix83_53 hinj83_53 hcardT83_53
      (fun i => conj_mem_of_fixedPoints _ _ (T83_53 i) (hfix83_53 i) _)
      ⟨83, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T83_53_2 Q2.hfix83_53_2 Q2.hinj83_53_2
      Q2.hcardT83_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_53_2 i) (Q2.hfix83_53_2 i) _)
      colCert_83_53_10.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T83_53
      hfix83_53 hinj83_53 hcardT83_53
      (fun i => conj_mem_of_fixedPoints _ _ (T83_53 i) (hfix83_53 i) _)
      ⟨83, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T83_53_2 Q2.hfix83_53_2 Q2.hinj83_53_2
      Q2.hcardT83_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_53_2 i) (Q2.hfix83_53_2 i) _)
      colCert_83_53_15.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T83_53
      hfix83_53 hinj83_53 hcardT83_53
      (fun i => conj_mem_of_fixedPoints _ _ (T83_53 i) (hfix83_53 i) _)
      ⟨83, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T83_53_2 Q2.hfix83_53_2 Q2.hinj83_53_2
      Q2.hcardT83_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_53_2 i) (Q2.hfix83_53_2 i) _)
      colCert_83_53_20.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_83_0 (hp : 0 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 0 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp)) T83_83
      hfix83_83 hinj83_83 hcardT83_83
      (fun i => conj_mem_of_fixedPoints _ _ (T83_83 i) (hfix83_83 i) _)
      ⟨83, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 0 hp) Q2.T83_83_2 Q2.hfix83_83_2 Q2.hinj83_83_2
      Q2.hcardT83_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_83_2 i) (Q2.hfix83_83_2 i) _)
      colCert_83_83_0.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_83_1 (hp : 1 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 1 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp)) T83_83
      hfix83_83 hinj83_83 hcardT83_83
      (fun i => conj_mem_of_fixedPoints _ _ (T83_83 i) (hfix83_83 i) _)
      ⟨83, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 1 hp) Q2.T83_83_2 Q2.hfix83_83_2 Q2.hinj83_83_2
      Q2.hcardT83_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_83_2 i) (Q2.hfix83_83_2 i) _)
      colCert_83_83_1.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_83_2 (hp : 2 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 2 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp)) T83_83
      hfix83_83 hinj83_83 hcardT83_83
      (fun i => conj_mem_of_fixedPoints _ _ (T83_83 i) (hfix83_83 i) _)
      ⟨83, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 2 hp) Q2.T83_83_2 Q2.hfix83_83_2 Q2.hinj83_83_2
      Q2.hcardT83_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_83_2 i) (Q2.hfix83_83_2 i) _)
      colCert_83_83_2.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_83_3 (hp : 3 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 3 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp)) T83_83
      hfix83_83 hinj83_83 hcardT83_83
      (fun i => conj_mem_of_fixedPoints _ _ (T83_83 i) (hfix83_83 i) _)
      ⟨83, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 3 hp) Q2.T83_83_2 Q2.hfix83_83_2 Q2.hinj83_83_2
      Q2.hcardT83_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_83_2 i) (Q2.hfix83_83_2 i) _)
      colCert_83_83_3.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_83_4 (hp : 4 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 4 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp)) T83_83
      hfix83_83 hinj83_83 hcardT83_83
      (fun i => conj_mem_of_fixedPoints _ _ (T83_83 i) (hfix83_83 i) _)
      ⟨83, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 4 hp) Q2.T83_83_2 Q2.hfix83_83_2 Q2.hinj83_83_2
      Q2.hcardT83_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_83_2 i) (Q2.hfix83_83_2 i) _)
      colCert_83_83_4.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_83_5 (hp : 5 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 5 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp)) T83_83
      hfix83_83 hinj83_83 hcardT83_83
      (fun i => conj_mem_of_fixedPoints _ _ (T83_83 i) (hfix83_83 i) _)
      ⟨83, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 5 hp) Q2.T83_83_2 Q2.hfix83_83_2 Q2.hinj83_83_2
      Q2.hcardT83_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_83_2 i) (Q2.hfix83_83_2 i) _)
      colCert_83_83_5.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_83_10 (hp : 10 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 10 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp)) T83_83
      hfix83_83 hinj83_83 hcardT83_83
      (fun i => conj_mem_of_fixedPoints _ _ (T83_83 i) (hfix83_83 i) _)
      ⟨83, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 10 hp) Q2.T83_83_2 Q2.hfix83_83_2 Q2.hinj83_83_2
      Q2.hcardT83_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_83_2 i) (Q2.hfix83_83_2 i) _)
      colCert_83_83_10.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_83_15 (hp : 15 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 15 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp)) T83_83
      hfix83_83 hinj83_83 hcardT83_83
      (fun i => conj_mem_of_fixedPoints _ _ (T83_83 i) (hfix83_83 i) _)
      ⟨83, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 15 hp) Q2.T83_83_2 Q2.hfix83_83_2 Q2.hinj83_83_2
      Q2.hcardT83_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_83_2 i) (Q2.hfix83_83_2 i) _)
      colCert_83_83_15.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_83_83_20 (hp : 20 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 83 []).length)
    (hq : (normIsRep.getD 83 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 20 hp)
        (rowE2 (⟨83, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp))
        (rowE1 (⟨83, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨83, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨83, by decide⟩ (listedAt ⟨83, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp)) T83_83
      hfix83_83 hinj83_83 hcardT83_83
      (fun i => conj_mem_of_fixedPoints _ _ (T83_83 i) (hfix83_83 i) _)
      ⟨83, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨83, by decide⟩ (Q2.listedAt ⟨83, by decide⟩
        (alnCheck_rep ⟨83, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 20 hp) Q2.T83_83_2 Q2.hfix83_83_2 Q2.hinj83_83_2
      Q2.hcardT83_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T83_83_2 i) (Q2.hfix83_83_2 i) _)
      colCert_83_83_20.hD ?_).symm
  rw [alnId_83 j hj]


theorem leaf_84_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T84_5
      hfix84_5 hinj84_5 hcardT84_5
      (fun i => conj_mem_of_fixedPoints _ _ (T84_5 i) (hfix84_5 i) _)
      ⟨84, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T84_5_2 Q2.hfix84_5_2 Q2.hinj84_5_2
      Q2.hcardT84_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_5_2 i) (Q2.hfix84_5_2 i) _)
      colCert_84_5_0.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T84_5
      hfix84_5 hinj84_5 hcardT84_5
      (fun i => conj_mem_of_fixedPoints _ _ (T84_5 i) (hfix84_5 i) _)
      ⟨84, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T84_5_2 Q2.hfix84_5_2 Q2.hinj84_5_2
      Q2.hcardT84_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_5_2 i) (Q2.hfix84_5_2 i) _)
      colCert_84_5_1.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T84_5
      hfix84_5 hinj84_5 hcardT84_5
      (fun i => conj_mem_of_fixedPoints _ _ (T84_5 i) (hfix84_5 i) _)
      ⟨84, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T84_5_2 Q2.hfix84_5_2 Q2.hinj84_5_2
      Q2.hcardT84_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_5_2 i) (Q2.hfix84_5_2 i) _)
      colCert_84_5_2.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T84_5
      hfix84_5 hinj84_5 hcardT84_5
      (fun i => conj_mem_of_fixedPoints _ _ (T84_5 i) (hfix84_5 i) _)
      ⟨84, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T84_5_2 Q2.hfix84_5_2 Q2.hinj84_5_2
      Q2.hcardT84_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_5_2 i) (Q2.hfix84_5_2 i) _)
      colCert_84_5_3.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T84_5
      hfix84_5 hinj84_5 hcardT84_5
      (fun i => conj_mem_of_fixedPoints _ _ (T84_5 i) (hfix84_5 i) _)
      ⟨84, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T84_5_2 Q2.hfix84_5_2 Q2.hinj84_5_2
      Q2.hcardT84_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_5_2 i) (Q2.hfix84_5_2 i) _)
      colCert_84_5_4.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T84_10
      hfix84_10 hinj84_10 hcardT84_10
      (fun i => conj_mem_of_fixedPoints _ _ (T84_10 i) (hfix84_10 i) _)
      ⟨84, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T84_10_2 Q2.hfix84_10_2 Q2.hinj84_10_2
      Q2.hcardT84_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_10_2 i) (Q2.hfix84_10_2 i) _)
      colCert_84_10_0.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T84_10
      hfix84_10 hinj84_10 hcardT84_10
      (fun i => conj_mem_of_fixedPoints _ _ (T84_10 i) (hfix84_10 i) _)
      ⟨84, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T84_10_2 Q2.hfix84_10_2 Q2.hinj84_10_2
      Q2.hcardT84_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_10_2 i) (Q2.hfix84_10_2 i) _)
      colCert_84_10_1.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T84_10
      hfix84_10 hinj84_10 hcardT84_10
      (fun i => conj_mem_of_fixedPoints _ _ (T84_10 i) (hfix84_10 i) _)
      ⟨84, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T84_10_2 Q2.hfix84_10_2 Q2.hinj84_10_2
      Q2.hcardT84_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_10_2 i) (Q2.hfix84_10_2 i) _)
      colCert_84_10_2.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T84_10
      hfix84_10 hinj84_10 hcardT84_10
      (fun i => conj_mem_of_fixedPoints _ _ (T84_10 i) (hfix84_10 i) _)
      ⟨84, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T84_10_2 Q2.hfix84_10_2 Q2.hinj84_10_2
      Q2.hcardT84_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_10_2 i) (Q2.hfix84_10_2 i) _)
      colCert_84_10_3.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T84_10
      hfix84_10 hinj84_10 hcardT84_10
      (fun i => conj_mem_of_fixedPoints _ _ (T84_10 i) (hfix84_10 i) _)
      ⟨84, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T84_10_2 Q2.hfix84_10_2 Q2.hinj84_10_2
      Q2.hcardT84_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_10_2 i) (Q2.hfix84_10_2 i) _)
      colCert_84_10_4.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T84_12
      hfix84_12 hinj84_12 hcardT84_12
      (fun i => conj_mem_of_fixedPoints _ _ (T84_12 i) (hfix84_12 i) _)
      ⟨84, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T84_12_2 Q2.hfix84_12_2 Q2.hinj84_12_2
      Q2.hcardT84_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_12_2 i) (Q2.hfix84_12_2 i) _)
      colCert_84_12_0.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T84_12
      hfix84_12 hinj84_12 hcardT84_12
      (fun i => conj_mem_of_fixedPoints _ _ (T84_12 i) (hfix84_12 i) _)
      ⟨84, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T84_12_2 Q2.hfix84_12_2 Q2.hinj84_12_2
      Q2.hcardT84_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_12_2 i) (Q2.hfix84_12_2 i) _)
      colCert_84_12_1.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T84_12
      hfix84_12 hinj84_12 hcardT84_12
      (fun i => conj_mem_of_fixedPoints _ _ (T84_12 i) (hfix84_12 i) _)
      ⟨84, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T84_12_2 Q2.hfix84_12_2 Q2.hinj84_12_2
      Q2.hcardT84_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_12_2 i) (Q2.hfix84_12_2 i) _)
      colCert_84_12_2.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T84_12
      hfix84_12 hinj84_12 hcardT84_12
      (fun i => conj_mem_of_fixedPoints _ _ (T84_12 i) (hfix84_12 i) _)
      ⟨84, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T84_12_2 Q2.hfix84_12_2 Q2.hinj84_12_2
      Q2.hcardT84_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_12_2 i) (Q2.hfix84_12_2 i) _)
      colCert_84_12_3.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T84_12
      hfix84_12 hinj84_12 hcardT84_12
      (fun i => conj_mem_of_fixedPoints _ _ (T84_12 i) (hfix84_12 i) _)
      ⟨84, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T84_12_2 Q2.hfix84_12_2 Q2.hinj84_12_2
      Q2.hcardT84_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_12_2 i) (Q2.hfix84_12_2 i) _)
      colCert_84_12_4.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T84_23
      hfix84_23 hinj84_23 hcardT84_23
      (fun i => conj_mem_of_fixedPoints _ _ (T84_23 i) (hfix84_23 i) _)
      ⟨84, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T84_23_2 Q2.hfix84_23_2 Q2.hinj84_23_2
      Q2.hcardT84_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_23_2 i) (Q2.hfix84_23_2 i) _)
      colCert_84_23_0.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T84_23
      hfix84_23 hinj84_23 hcardT84_23
      (fun i => conj_mem_of_fixedPoints _ _ (T84_23 i) (hfix84_23 i) _)
      ⟨84, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T84_23_2 Q2.hfix84_23_2 Q2.hinj84_23_2
      Q2.hcardT84_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_23_2 i) (Q2.hfix84_23_2 i) _)
      colCert_84_23_1.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T84_23
      hfix84_23 hinj84_23 hcardT84_23
      (fun i => conj_mem_of_fixedPoints _ _ (T84_23 i) (hfix84_23 i) _)
      ⟨84, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T84_23_2 Q2.hfix84_23_2 Q2.hinj84_23_2
      Q2.hcardT84_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_23_2 i) (Q2.hfix84_23_2 i) _)
      colCert_84_23_2.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T84_23
      hfix84_23 hinj84_23 hcardT84_23
      (fun i => conj_mem_of_fixedPoints _ _ (T84_23 i) (hfix84_23 i) _)
      ⟨84, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T84_23_2 Q2.hfix84_23_2 Q2.hinj84_23_2
      Q2.hcardT84_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_23_2 i) (Q2.hfix84_23_2 i) _)
      colCert_84_23_3.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T84_23
      hfix84_23 hinj84_23 hcardT84_23
      (fun i => conj_mem_of_fixedPoints _ _ (T84_23 i) (hfix84_23 i) _)
      ⟨84, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T84_23_2 Q2.hfix84_23_2 Q2.hinj84_23_2
      Q2.hcardT84_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_23_2 i) (Q2.hfix84_23_2 i) _)
      colCert_84_23_4.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T84_23
      hfix84_23 hinj84_23 hcardT84_23
      (fun i => conj_mem_of_fixedPoints _ _ (T84_23 i) (hfix84_23 i) _)
      ⟨84, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T84_23_2 Q2.hfix84_23_2 Q2.hinj84_23_2
      Q2.hcardT84_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_23_2 i) (Q2.hfix84_23_2 i) _)
      colCert_84_23_5.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T84_23
      hfix84_23 hinj84_23 hcardT84_23
      (fun i => conj_mem_of_fixedPoints _ _ (T84_23 i) (hfix84_23 i) _)
      ⟨84, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T84_23_2 Q2.hfix84_23_2 Q2.hinj84_23_2
      Q2.hcardT84_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_23_2 i) (Q2.hfix84_23_2 i) _)
      colCert_84_23_10.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T84_23
      hfix84_23 hinj84_23 hcardT84_23
      (fun i => conj_mem_of_fixedPoints _ _ (T84_23 i) (hfix84_23 i) _)
      ⟨84, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T84_23_2 Q2.hfix84_23_2 Q2.hinj84_23_2
      Q2.hcardT84_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_23_2 i) (Q2.hfix84_23_2 i) _)
      colCert_84_23_15.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T84_23
      hfix84_23 hinj84_23 hcardT84_23
      (fun i => conj_mem_of_fixedPoints _ _ (T84_23 i) (hfix84_23 i) _)
      ⟨84, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T84_23_2 Q2.hfix84_23_2 Q2.hinj84_23_2
      Q2.hcardT84_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_23_2 i) (Q2.hfix84_23_2 i) _)
      colCert_84_23_20.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T84_53
      hfix84_53 hinj84_53 hcardT84_53
      (fun i => conj_mem_of_fixedPoints _ _ (T84_53 i) (hfix84_53 i) _)
      ⟨84, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T84_53_2 Q2.hfix84_53_2 Q2.hinj84_53_2
      Q2.hcardT84_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_53_2 i) (Q2.hfix84_53_2 i) _)
      colCert_84_53_0.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T84_53
      hfix84_53 hinj84_53 hcardT84_53
      (fun i => conj_mem_of_fixedPoints _ _ (T84_53 i) (hfix84_53 i) _)
      ⟨84, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T84_53_2 Q2.hfix84_53_2 Q2.hinj84_53_2
      Q2.hcardT84_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_53_2 i) (Q2.hfix84_53_2 i) _)
      colCert_84_53_1.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T84_53
      hfix84_53 hinj84_53 hcardT84_53
      (fun i => conj_mem_of_fixedPoints _ _ (T84_53 i) (hfix84_53 i) _)
      ⟨84, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T84_53_2 Q2.hfix84_53_2 Q2.hinj84_53_2
      Q2.hcardT84_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_53_2 i) (Q2.hfix84_53_2 i) _)
      colCert_84_53_2.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T84_53
      hfix84_53 hinj84_53 hcardT84_53
      (fun i => conj_mem_of_fixedPoints _ _ (T84_53 i) (hfix84_53 i) _)
      ⟨84, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T84_53_2 Q2.hfix84_53_2 Q2.hinj84_53_2
      Q2.hcardT84_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_53_2 i) (Q2.hfix84_53_2 i) _)
      colCert_84_53_3.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T84_53
      hfix84_53 hinj84_53 hcardT84_53
      (fun i => conj_mem_of_fixedPoints _ _ (T84_53 i) (hfix84_53 i) _)
      ⟨84, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T84_53_2 Q2.hfix84_53_2 Q2.hinj84_53_2
      Q2.hcardT84_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_53_2 i) (Q2.hfix84_53_2 i) _)
      colCert_84_53_4.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T84_53
      hfix84_53 hinj84_53 hcardT84_53
      (fun i => conj_mem_of_fixedPoints _ _ (T84_53 i) (hfix84_53 i) _)
      ⟨84, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T84_53_2 Q2.hfix84_53_2 Q2.hinj84_53_2
      Q2.hcardT84_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_53_2 i) (Q2.hfix84_53_2 i) _)
      colCert_84_53_5.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T84_53
      hfix84_53 hinj84_53 hcardT84_53
      (fun i => conj_mem_of_fixedPoints _ _ (T84_53 i) (hfix84_53 i) _)
      ⟨84, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T84_53_2 Q2.hfix84_53_2 Q2.hinj84_53_2
      Q2.hcardT84_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_53_2 i) (Q2.hfix84_53_2 i) _)
      colCert_84_53_10.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T84_53
      hfix84_53 hinj84_53 hcardT84_53
      (fun i => conj_mem_of_fixedPoints _ _ (T84_53 i) (hfix84_53 i) _)
      ⟨84, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T84_53_2 Q2.hfix84_53_2 Q2.hinj84_53_2
      Q2.hcardT84_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_53_2 i) (Q2.hfix84_53_2 i) _)
      colCert_84_53_15.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T84_53
      hfix84_53 hinj84_53 hcardT84_53
      (fun i => conj_mem_of_fixedPoints _ _ (T84_53 i) (hfix84_53 i) _)
      ⟨84, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T84_53_2 Q2.hfix84_53_2 Q2.hinj84_53_2
      Q2.hcardT84_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_53_2 i) (Q2.hfix84_53_2 i) _)
      colCert_84_53_20.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_84_0 (hp : 0 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 0 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp)) T84_84
      hfix84_84 hinj84_84 hcardT84_84
      (fun i => conj_mem_of_fixedPoints _ _ (T84_84 i) (hfix84_84 i) _)
      ⟨84, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 0 hp) Q2.T84_84_2 Q2.hfix84_84_2 Q2.hinj84_84_2
      Q2.hcardT84_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_84_2 i) (Q2.hfix84_84_2 i) _)
      colCert_84_84_0.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_84_1 (hp : 1 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 1 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp)) T84_84
      hfix84_84 hinj84_84 hcardT84_84
      (fun i => conj_mem_of_fixedPoints _ _ (T84_84 i) (hfix84_84 i) _)
      ⟨84, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 1 hp) Q2.T84_84_2 Q2.hfix84_84_2 Q2.hinj84_84_2
      Q2.hcardT84_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_84_2 i) (Q2.hfix84_84_2 i) _)
      colCert_84_84_1.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_84_2 (hp : 2 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 2 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp)) T84_84
      hfix84_84 hinj84_84 hcardT84_84
      (fun i => conj_mem_of_fixedPoints _ _ (T84_84 i) (hfix84_84 i) _)
      ⟨84, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 2 hp) Q2.T84_84_2 Q2.hfix84_84_2 Q2.hinj84_84_2
      Q2.hcardT84_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_84_2 i) (Q2.hfix84_84_2 i) _)
      colCert_84_84_2.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_84_3 (hp : 3 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 3 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp)) T84_84
      hfix84_84 hinj84_84 hcardT84_84
      (fun i => conj_mem_of_fixedPoints _ _ (T84_84 i) (hfix84_84 i) _)
      ⟨84, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 3 hp) Q2.T84_84_2 Q2.hfix84_84_2 Q2.hinj84_84_2
      Q2.hcardT84_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_84_2 i) (Q2.hfix84_84_2 i) _)
      colCert_84_84_3.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_84_4 (hp : 4 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 4 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp)) T84_84
      hfix84_84 hinj84_84 hcardT84_84
      (fun i => conj_mem_of_fixedPoints _ _ (T84_84 i) (hfix84_84 i) _)
      ⟨84, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 4 hp) Q2.T84_84_2 Q2.hfix84_84_2 Q2.hinj84_84_2
      Q2.hcardT84_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_84_2 i) (Q2.hfix84_84_2 i) _)
      colCert_84_84_4.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_84_5 (hp : 5 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 5 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp)) T84_84
      hfix84_84 hinj84_84 hcardT84_84
      (fun i => conj_mem_of_fixedPoints _ _ (T84_84 i) (hfix84_84 i) _)
      ⟨84, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 5 hp) Q2.T84_84_2 Q2.hfix84_84_2 Q2.hinj84_84_2
      Q2.hcardT84_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_84_2 i) (Q2.hfix84_84_2 i) _)
      colCert_84_84_5.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_84_10 (hp : 10 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 10 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp)) T84_84
      hfix84_84 hinj84_84 hcardT84_84
      (fun i => conj_mem_of_fixedPoints _ _ (T84_84 i) (hfix84_84 i) _)
      ⟨84, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 10 hp) Q2.T84_84_2 Q2.hfix84_84_2 Q2.hinj84_84_2
      Q2.hcardT84_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_84_2 i) (Q2.hfix84_84_2 i) _)
      colCert_84_84_10.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_84_15 (hp : 15 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 15 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp)) T84_84
      hfix84_84 hinj84_84 hcardT84_84
      (fun i => conj_mem_of_fixedPoints _ _ (T84_84 i) (hfix84_84 i) _)
      ⟨84, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 15 hp) Q2.T84_84_2 Q2.hfix84_84_2 Q2.hinj84_84_2
      Q2.hcardT84_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_84_2 i) (Q2.hfix84_84_2 i) _)
      colCert_84_84_15.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_84_84_20 (hp : 20 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 84 []).length)
    (hq : (normIsRep.getD 84 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 20 hp)
        (rowE2 (⟨84, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp))
        (rowE1 (⟨84, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨84, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨84, by decide⟩ (listedAt ⟨84, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp)) T84_84
      hfix84_84 hinj84_84 hcardT84_84
      (fun i => conj_mem_of_fixedPoints _ _ (T84_84 i) (hfix84_84 i) _)
      ⟨84, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨84, by decide⟩ (Q2.listedAt ⟨84, by decide⟩
        (alnCheck_rep ⟨84, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 20 hp) Q2.T84_84_2 Q2.hfix84_84_2 Q2.hinj84_84_2
      Q2.hcardT84_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T84_84_2 i) (Q2.hfix84_84_2 i) _)
      colCert_84_84_20.hD ?_).symm
  rw [alnId_84 j hj]


theorem leaf_85_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T85_2
      hfix85_2 hinj85_2 hcardT85_2
      (fun i => conj_mem_of_fixedPoints _ _ (T85_2 i) (hfix85_2 i) _)
      ⟨85, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T85_2_2 Q2.hfix85_2_2 Q2.hinj85_2_2
      Q2.hcardT85_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_2_2 i) (Q2.hfix85_2_2 i) _)
      colCert_85_2_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T85_2
      hfix85_2 hinj85_2 hcardT85_2
      (fun i => conj_mem_of_fixedPoints _ _ (T85_2 i) (hfix85_2 i) _)
      ⟨85, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T85_2_2 Q2.hfix85_2_2 Q2.hinj85_2_2
      Q2.hcardT85_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_2_2 i) (Q2.hfix85_2_2 i) _)
      colCert_85_2_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T85_2
      hfix85_2 hinj85_2 hcardT85_2
      (fun i => conj_mem_of_fixedPoints _ _ (T85_2 i) (hfix85_2 i) _)
      ⟨85, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T85_2_2 Q2.hfix85_2_2 Q2.hinj85_2_2
      Q2.hcardT85_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_2_2 i) (Q2.hfix85_2_2 i) _)
      colCert_85_2_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T85_2
      hfix85_2 hinj85_2 hcardT85_2
      (fun i => conj_mem_of_fixedPoints _ _ (T85_2 i) (hfix85_2 i) _)
      ⟨85, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T85_2_2 Q2.hfix85_2_2 Q2.hinj85_2_2
      Q2.hcardT85_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_2_2 i) (Q2.hfix85_2_2 i) _)
      colCert_85_2_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T85_2
      hfix85_2 hinj85_2 hcardT85_2
      (fun i => conj_mem_of_fixedPoints _ _ (T85_2 i) (hfix85_2 i) _)
      ⟨85, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T85_2_2 Q2.hfix85_2_2 Q2.hinj85_2_2
      Q2.hcardT85_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_2_2 i) (Q2.hfix85_2_2 i) _)
      colCert_85_2_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T85_3
      hfix85_3 hinj85_3 hcardT85_3
      (fun i => conj_mem_of_fixedPoints _ _ (T85_3 i) (hfix85_3 i) _)
      ⟨85, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T85_3_2 Q2.hfix85_3_2 Q2.hinj85_3_2
      Q2.hcardT85_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_3_2 i) (Q2.hfix85_3_2 i) _)
      colCert_85_3_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T85_3
      hfix85_3 hinj85_3 hcardT85_3
      (fun i => conj_mem_of_fixedPoints _ _ (T85_3 i) (hfix85_3 i) _)
      ⟨85, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T85_3_2 Q2.hfix85_3_2 Q2.hinj85_3_2
      Q2.hcardT85_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_3_2 i) (Q2.hfix85_3_2 i) _)
      colCert_85_3_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T85_3
      hfix85_3 hinj85_3 hcardT85_3
      (fun i => conj_mem_of_fixedPoints _ _ (T85_3 i) (hfix85_3 i) _)
      ⟨85, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T85_3_2 Q2.hfix85_3_2 Q2.hinj85_3_2
      Q2.hcardT85_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_3_2 i) (Q2.hfix85_3_2 i) _)
      colCert_85_3_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T85_3
      hfix85_3 hinj85_3 hcardT85_3
      (fun i => conj_mem_of_fixedPoints _ _ (T85_3 i) (hfix85_3 i) _)
      ⟨85, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T85_3_2 Q2.hfix85_3_2 Q2.hinj85_3_2
      Q2.hcardT85_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_3_2 i) (Q2.hfix85_3_2 i) _)
      colCert_85_3_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T85_3
      hfix85_3 hinj85_3 hcardT85_3
      (fun i => conj_mem_of_fixedPoints _ _ (T85_3 i) (hfix85_3 i) _)
      ⟨85, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T85_3_2 Q2.hfix85_3_2 Q2.hinj85_3_2
      Q2.hcardT85_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_3_2 i) (Q2.hfix85_3_2 i) _)
      colCert_85_3_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T85_4
      hfix85_4 hinj85_4 hcardT85_4
      (fun i => conj_mem_of_fixedPoints _ _ (T85_4 i) (hfix85_4 i) _)
      ⟨85, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T85_4_2 Q2.hfix85_4_2 Q2.hinj85_4_2
      Q2.hcardT85_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_4_2 i) (Q2.hfix85_4_2 i) _)
      colCert_85_4_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T85_4
      hfix85_4 hinj85_4 hcardT85_4
      (fun i => conj_mem_of_fixedPoints _ _ (T85_4 i) (hfix85_4 i) _)
      ⟨85, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T85_4_2 Q2.hfix85_4_2 Q2.hinj85_4_2
      Q2.hcardT85_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_4_2 i) (Q2.hfix85_4_2 i) _)
      colCert_85_4_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T85_4
      hfix85_4 hinj85_4 hcardT85_4
      (fun i => conj_mem_of_fixedPoints _ _ (T85_4 i) (hfix85_4 i) _)
      ⟨85, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T85_4_2 Q2.hfix85_4_2 Q2.hinj85_4_2
      Q2.hcardT85_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_4_2 i) (Q2.hfix85_4_2 i) _)
      colCert_85_4_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T85_4
      hfix85_4 hinj85_4 hcardT85_4
      (fun i => conj_mem_of_fixedPoints _ _ (T85_4 i) (hfix85_4 i) _)
      ⟨85, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T85_4_2 Q2.hfix85_4_2 Q2.hinj85_4_2
      Q2.hcardT85_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_4_2 i) (Q2.hfix85_4_2 i) _)
      colCert_85_4_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T85_4
      hfix85_4 hinj85_4 hcardT85_4
      (fun i => conj_mem_of_fixedPoints _ _ (T85_4 i) (hfix85_4 i) _)
      ⟨85, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T85_4_2 Q2.hfix85_4_2 Q2.hinj85_4_2
      Q2.hcardT85_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_4_2 i) (Q2.hfix85_4_2 i) _)
      colCert_85_4_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T85_5
      hfix85_5 hinj85_5 hcardT85_5
      (fun i => conj_mem_of_fixedPoints _ _ (T85_5 i) (hfix85_5 i) _)
      ⟨85, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T85_5_2 Q2.hfix85_5_2 Q2.hinj85_5_2
      Q2.hcardT85_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_5_2 i) (Q2.hfix85_5_2 i) _)
      colCert_85_5_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T85_5
      hfix85_5 hinj85_5 hcardT85_5
      (fun i => conj_mem_of_fixedPoints _ _ (T85_5 i) (hfix85_5 i) _)
      ⟨85, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T85_5_2 Q2.hfix85_5_2 Q2.hinj85_5_2
      Q2.hcardT85_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_5_2 i) (Q2.hfix85_5_2 i) _)
      colCert_85_5_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T85_5
      hfix85_5 hinj85_5 hcardT85_5
      (fun i => conj_mem_of_fixedPoints _ _ (T85_5 i) (hfix85_5 i) _)
      ⟨85, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T85_5_2 Q2.hfix85_5_2 Q2.hinj85_5_2
      Q2.hcardT85_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_5_2 i) (Q2.hfix85_5_2 i) _)
      colCert_85_5_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T85_5
      hfix85_5 hinj85_5 hcardT85_5
      (fun i => conj_mem_of_fixedPoints _ _ (T85_5 i) (hfix85_5 i) _)
      ⟨85, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T85_5_2 Q2.hfix85_5_2 Q2.hinj85_5_2
      Q2.hcardT85_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_5_2 i) (Q2.hfix85_5_2 i) _)
      colCert_85_5_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T85_5
      hfix85_5 hinj85_5 hcardT85_5
      (fun i => conj_mem_of_fixedPoints _ _ (T85_5 i) (hfix85_5 i) _)
      ⟨85, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T85_5_2 Q2.hfix85_5_2 Q2.hinj85_5_2
      Q2.hcardT85_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_5_2 i) (Q2.hfix85_5_2 i) _)
      colCert_85_5_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T85_9
      hfix85_9 hinj85_9 hcardT85_9
      (fun i => conj_mem_of_fixedPoints _ _ (T85_9 i) (hfix85_9 i) _)
      ⟨85, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T85_9_2 Q2.hfix85_9_2 Q2.hinj85_9_2
      Q2.hcardT85_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_9_2 i) (Q2.hfix85_9_2 i) _)
      colCert_85_9_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T85_9
      hfix85_9 hinj85_9 hcardT85_9
      (fun i => conj_mem_of_fixedPoints _ _ (T85_9 i) (hfix85_9 i) _)
      ⟨85, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T85_9_2 Q2.hfix85_9_2 Q2.hinj85_9_2
      Q2.hcardT85_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_9_2 i) (Q2.hfix85_9_2 i) _)
      colCert_85_9_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T85_9
      hfix85_9 hinj85_9 hcardT85_9
      (fun i => conj_mem_of_fixedPoints _ _ (T85_9 i) (hfix85_9 i) _)
      ⟨85, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T85_9_2 Q2.hfix85_9_2 Q2.hinj85_9_2
      Q2.hcardT85_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_9_2 i) (Q2.hfix85_9_2 i) _)
      colCert_85_9_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T85_9
      hfix85_9 hinj85_9 hcardT85_9
      (fun i => conj_mem_of_fixedPoints _ _ (T85_9 i) (hfix85_9 i) _)
      ⟨85, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T85_9_2 Q2.hfix85_9_2 Q2.hinj85_9_2
      Q2.hcardT85_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_9_2 i) (Q2.hfix85_9_2 i) _)
      colCert_85_9_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T85_9
      hfix85_9 hinj85_9 hcardT85_9
      (fun i => conj_mem_of_fixedPoints _ _ (T85_9 i) (hfix85_9 i) _)
      ⟨85, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T85_9_2 Q2.hfix85_9_2 Q2.hinj85_9_2
      Q2.hcardT85_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_9_2 i) (Q2.hfix85_9_2 i) _)
      colCert_85_9_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T85_11
      hfix85_11 hinj85_11 hcardT85_11
      (fun i => conj_mem_of_fixedPoints _ _ (T85_11 i) (hfix85_11 i) _)
      ⟨85, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T85_11_2 Q2.hfix85_11_2 Q2.hinj85_11_2
      Q2.hcardT85_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_11_2 i) (Q2.hfix85_11_2 i) _)
      colCert_85_11_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T85_11
      hfix85_11 hinj85_11 hcardT85_11
      (fun i => conj_mem_of_fixedPoints _ _ (T85_11 i) (hfix85_11 i) _)
      ⟨85, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T85_11_2 Q2.hfix85_11_2 Q2.hinj85_11_2
      Q2.hcardT85_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_11_2 i) (Q2.hfix85_11_2 i) _)
      colCert_85_11_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T85_11
      hfix85_11 hinj85_11 hcardT85_11
      (fun i => conj_mem_of_fixedPoints _ _ (T85_11 i) (hfix85_11 i) _)
      ⟨85, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T85_11_2 Q2.hfix85_11_2 Q2.hinj85_11_2
      Q2.hcardT85_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_11_2 i) (Q2.hfix85_11_2 i) _)
      colCert_85_11_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T85_11
      hfix85_11 hinj85_11 hcardT85_11
      (fun i => conj_mem_of_fixedPoints _ _ (T85_11 i) (hfix85_11 i) _)
      ⟨85, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T85_11_2 Q2.hfix85_11_2 Q2.hinj85_11_2
      Q2.hcardT85_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_11_2 i) (Q2.hfix85_11_2 i) _)
      colCert_85_11_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T85_11
      hfix85_11 hinj85_11 hcardT85_11
      (fun i => conj_mem_of_fixedPoints _ _ (T85_11 i) (hfix85_11 i) _)
      ⟨85, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T85_11_2 Q2.hfix85_11_2 Q2.hinj85_11_2
      Q2.hcardT85_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_11_2 i) (Q2.hfix85_11_2 i) _)
      colCert_85_11_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T85_12
      hfix85_12 hinj85_12 hcardT85_12
      (fun i => conj_mem_of_fixedPoints _ _ (T85_12 i) (hfix85_12 i) _)
      ⟨85, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T85_12_2 Q2.hfix85_12_2 Q2.hinj85_12_2
      Q2.hcardT85_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_12_2 i) (Q2.hfix85_12_2 i) _)
      colCert_85_12_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T85_12
      hfix85_12 hinj85_12 hcardT85_12
      (fun i => conj_mem_of_fixedPoints _ _ (T85_12 i) (hfix85_12 i) _)
      ⟨85, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T85_12_2 Q2.hfix85_12_2 Q2.hinj85_12_2
      Q2.hcardT85_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_12_2 i) (Q2.hfix85_12_2 i) _)
      colCert_85_12_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T85_12
      hfix85_12 hinj85_12 hcardT85_12
      (fun i => conj_mem_of_fixedPoints _ _ (T85_12 i) (hfix85_12 i) _)
      ⟨85, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T85_12_2 Q2.hfix85_12_2 Q2.hinj85_12_2
      Q2.hcardT85_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_12_2 i) (Q2.hfix85_12_2 i) _)
      colCert_85_12_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T85_12
      hfix85_12 hinj85_12 hcardT85_12
      (fun i => conj_mem_of_fixedPoints _ _ (T85_12 i) (hfix85_12 i) _)
      ⟨85, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T85_12_2 Q2.hfix85_12_2 Q2.hinj85_12_2
      Q2.hcardT85_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_12_2 i) (Q2.hfix85_12_2 i) _)
      colCert_85_12_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T85_12
      hfix85_12 hinj85_12 hcardT85_12
      (fun i => conj_mem_of_fixedPoints _ _ (T85_12 i) (hfix85_12 i) _)
      ⟨85, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T85_12_2 Q2.hfix85_12_2 Q2.hinj85_12_2
      Q2.hcardT85_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_12_2 i) (Q2.hfix85_12_2 i) _)
      colCert_85_12_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_0 (hp : 0 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 0 (transLenTr ⟨14, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 0 (transLenTr ⟨14, by decide⟩ 0 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 0 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_1 (hp : 1 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 1 (transLenTr ⟨14, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 1 (transLenTr ⟨14, by decide⟩ 1 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 1 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_2 (hp : 2 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 2 (transLenTr ⟨14, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 2 (transLenTr ⟨14, by decide⟩ 2 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 2 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_3 (hp : 3 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 3 (transLenTr ⟨14, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 3 (transLenTr ⟨14, by decide⟩ 3 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 3 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_4 (hp : 4 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 4 (transLenTr ⟨14, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 4 (transLenTr ⟨14, by decide⟩ 4 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 4 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_5 (hp : 5 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 5 (transLenTr ⟨14, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 5 (transLenTr ⟨14, by decide⟩ 5 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 5 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_6 (hp : 6 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 6 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 6 (transLenTr ⟨14, by decide⟩ 6 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 6 (transLenTr ⟨14, by decide⟩ 6 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 6 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_6.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_7 (hp : 7 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 7 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 7 (transLenTr ⟨14, by decide⟩ 7 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 7 (transLenTr ⟨14, by decide⟩ 7 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 7 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_7.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_8 (hp : 8 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 8 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 8 (transLenTr ⟨14, by decide⟩ 8 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 8 (transLenTr ⟨14, by decide⟩ 8 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 8 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_8.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_9 (hp : 9 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 9 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 9 (transLenTr ⟨14, by decide⟩ 9 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 9 (transLenTr ⟨14, by decide⟩ 9 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 9 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_9.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_10 (hp : 10 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 10 (transLenTr ⟨14, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 10 (transLenTr ⟨14, by decide⟩ 10 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 10 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_11 (hp : 11 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 11 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 11 (transLenTr ⟨14, by decide⟩ 11 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 11 (transLenTr ⟨14, by decide⟩ 11 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 11 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_11.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_12 (hp : 12 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 12 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 12 (transLenTr ⟨14, by decide⟩ 12 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 12 (transLenTr ⟨14, by decide⟩ 12 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 12 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_12.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_13 (hp : 13 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 13 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 13 (transLenTr ⟨14, by decide⟩ 13 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 13 (transLenTr ⟨14, by decide⟩ 13 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 13 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_13.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_14 (hp : 14 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 14 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 14 (transLenTr ⟨14, by decide⟩ 14 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 14 (transLenTr ⟨14, by decide⟩ 14 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 14 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_14.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_15 (hp : 15 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 15 (transLenTr ⟨14, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 15 (transLenTr ⟨14, by decide⟩ 15 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 15 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_16 (hp : 16 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 16 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 16 (transLenTr ⟨14, by decide⟩ 16 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 16 (transLenTr ⟨14, by decide⟩ 16 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 16 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_16.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_17 (hp : 17 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 17 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 17 (transLenTr ⟨14, by decide⟩ 17 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 17 (transLenTr ⟨14, by decide⟩ 17 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 17 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_17.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_18 (hp : 18 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 18 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 18 (transLenTr ⟨14, by decide⟩ 18 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 18 (transLenTr ⟨14, by decide⟩ 18 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 18 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_18.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_19 (hp : 19 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 19 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 19 (transLenTr ⟨14, by decide⟩ 19 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 19 (transLenTr ⟨14, by decide⟩ 19 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 19 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_19.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_20 (hp : 20 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 20 (transLenTr ⟨14, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 20 (transLenTr ⟨14, by decide⟩ 20 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 20 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_21 (hp : 21 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 21 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 21 (transLenTr ⟨14, by decide⟩ 21 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 21 (transLenTr ⟨14, by decide⟩ 21 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 21 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_21.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_22 (hp : 22 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 22 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 22 (transLenTr ⟨14, by decide⟩ 22 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 22 (transLenTr ⟨14, by decide⟩ 22 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 22 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_22.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_23 (hp : 23 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 23 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 23 (transLenTr ⟨14, by decide⟩ 23 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 23 (transLenTr ⟨14, by decide⟩ 23 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 23 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_23.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_14_24 (hp : 24 < (Q2.transData.getD 14 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨14, by decide⟩ : Fin 148)) (colE2 ⟨14, by decide⟩ 24 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨14, by decide⟩ : Fin 148))
        (colE1 ⟨14, by decide⟩ 24 (transLenTr ⟨14, by decide⟩ 24 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨14, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨14, by decide⟩ 24 (transLenTr ⟨14, by decide⟩ 24 hp)) T85_14
      hfix85_14 hinj85_14 hcardT85_14
      (fun i => conj_mem_of_fixedPoints _ _ (T85_14 i) (hfix85_14 i) _)
      ⟨85, by decide⟩ ⟨14, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨14, by decide⟩ 24 hp) Q2.T85_14_2 Q2.hfix85_14_2 Q2.hinj85_14_2
      Q2.hcardT85_14_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_14_2 i) (Q2.hfix85_14_2 i) _)
      colCert_85_14_24.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_0 (hp : 0 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 0 (transLenTr ⟨15, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 0 (transLenTr ⟨15, by decide⟩ 0 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 0 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_1 (hp : 1 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 1 (transLenTr ⟨15, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 1 (transLenTr ⟨15, by decide⟩ 1 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 1 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_2 (hp : 2 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 2 (transLenTr ⟨15, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 2 (transLenTr ⟨15, by decide⟩ 2 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 2 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_3 (hp : 3 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 3 (transLenTr ⟨15, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 3 (transLenTr ⟨15, by decide⟩ 3 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 3 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_4 (hp : 4 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 4 (transLenTr ⟨15, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 4 (transLenTr ⟨15, by decide⟩ 4 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 4 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_5 (hp : 5 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 5 (transLenTr ⟨15, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 5 (transLenTr ⟨15, by decide⟩ 5 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 5 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_6 (hp : 6 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 6 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 6 (transLenTr ⟨15, by decide⟩ 6 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 6 (transLenTr ⟨15, by decide⟩ 6 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 6 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_6.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_7 (hp : 7 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 7 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 7 (transLenTr ⟨15, by decide⟩ 7 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 7 (transLenTr ⟨15, by decide⟩ 7 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 7 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_7.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_8 (hp : 8 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 8 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 8 (transLenTr ⟨15, by decide⟩ 8 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 8 (transLenTr ⟨15, by decide⟩ 8 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 8 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_8.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_9 (hp : 9 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 9 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 9 (transLenTr ⟨15, by decide⟩ 9 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 9 (transLenTr ⟨15, by decide⟩ 9 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 9 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_9.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_10 (hp : 10 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 10 (transLenTr ⟨15, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 10 (transLenTr ⟨15, by decide⟩ 10 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 10 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_11 (hp : 11 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 11 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 11 (transLenTr ⟨15, by decide⟩ 11 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 11 (transLenTr ⟨15, by decide⟩ 11 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 11 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_11.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_12 (hp : 12 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 12 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 12 (transLenTr ⟨15, by decide⟩ 12 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 12 (transLenTr ⟨15, by decide⟩ 12 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 12 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_12.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_13 (hp : 13 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 13 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 13 (transLenTr ⟨15, by decide⟩ 13 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 13 (transLenTr ⟨15, by decide⟩ 13 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 13 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_13.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_14 (hp : 14 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 14 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 14 (transLenTr ⟨15, by decide⟩ 14 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 14 (transLenTr ⟨15, by decide⟩ 14 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 14 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_14.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_15 (hp : 15 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 15 (transLenTr ⟨15, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 15 (transLenTr ⟨15, by decide⟩ 15 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 15 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_16 (hp : 16 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 16 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 16 (transLenTr ⟨15, by decide⟩ 16 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 16 (transLenTr ⟨15, by decide⟩ 16 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 16 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_16.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_17 (hp : 17 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 17 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 17 (transLenTr ⟨15, by decide⟩ 17 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 17 (transLenTr ⟨15, by decide⟩ 17 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 17 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_17.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_18 (hp : 18 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 18 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 18 (transLenTr ⟨15, by decide⟩ 18 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 18 (transLenTr ⟨15, by decide⟩ 18 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 18 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_18.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_19 (hp : 19 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 19 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 19 (transLenTr ⟨15, by decide⟩ 19 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 19 (transLenTr ⟨15, by decide⟩ 19 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 19 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_19.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_20 (hp : 20 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 20 (transLenTr ⟨15, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 20 (transLenTr ⟨15, by decide⟩ 20 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 20 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_21 (hp : 21 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 21 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 21 (transLenTr ⟨15, by decide⟩ 21 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 21 (transLenTr ⟨15, by decide⟩ 21 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 21 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_21.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_22 (hp : 22 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 22 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 22 (transLenTr ⟨15, by decide⟩ 22 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 22 (transLenTr ⟨15, by decide⟩ 22 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 22 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_22.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_23 (hp : 23 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 23 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 23 (transLenTr ⟨15, by decide⟩ 23 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 23 (transLenTr ⟨15, by decide⟩ 23 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 23 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_23.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_15_24 (hp : 24 < (Q2.transData.getD 15 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨15, by decide⟩ : Fin 148)) (colE2 ⟨15, by decide⟩ 24 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨15, by decide⟩ : Fin 148))
        (colE1 ⟨15, by decide⟩ 24 (transLenTr ⟨15, by decide⟩ 24 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨15, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨15, by decide⟩ 24 (transLenTr ⟨15, by decide⟩ 24 hp)) T85_15
      hfix85_15 hinj85_15 hcardT85_15
      (fun i => conj_mem_of_fixedPoints _ _ (T85_15 i) (hfix85_15 i) _)
      ⟨85, by decide⟩ ⟨15, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨15, by decide⟩ 24 hp) Q2.T85_15_2 Q2.hfix85_15_2 Q2.hinj85_15_2
      Q2.hcardT85_15_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_15_2 i) (Q2.hfix85_15_2 i) _)
      colCert_85_15_24.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_0 (hp : 0 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 0 (transLenTr ⟨16, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 0 (transLenTr ⟨16, by decide⟩ 0 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 0 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_1 (hp : 1 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 1 (transLenTr ⟨16, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 1 (transLenTr ⟨16, by decide⟩ 1 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 1 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_2 (hp : 2 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 2 (transLenTr ⟨16, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 2 (transLenTr ⟨16, by decide⟩ 2 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 2 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_3 (hp : 3 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 3 (transLenTr ⟨16, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 3 (transLenTr ⟨16, by decide⟩ 3 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 3 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_4 (hp : 4 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 4 (transLenTr ⟨16, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 4 (transLenTr ⟨16, by decide⟩ 4 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 4 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_5 (hp : 5 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 5 (transLenTr ⟨16, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 5 (transLenTr ⟨16, by decide⟩ 5 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 5 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_6 (hp : 6 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 6 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 6 (transLenTr ⟨16, by decide⟩ 6 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 6 (transLenTr ⟨16, by decide⟩ 6 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 6 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_6.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_7 (hp : 7 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 7 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 7 (transLenTr ⟨16, by decide⟩ 7 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 7 (transLenTr ⟨16, by decide⟩ 7 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 7 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_7.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_8 (hp : 8 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 8 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 8 (transLenTr ⟨16, by decide⟩ 8 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 8 (transLenTr ⟨16, by decide⟩ 8 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 8 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_8.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_9 (hp : 9 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 9 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 9 (transLenTr ⟨16, by decide⟩ 9 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 9 (transLenTr ⟨16, by decide⟩ 9 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 9 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_9.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_10 (hp : 10 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 10 (transLenTr ⟨16, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 10 (transLenTr ⟨16, by decide⟩ 10 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 10 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_11 (hp : 11 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 11 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 11 (transLenTr ⟨16, by decide⟩ 11 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 11 (transLenTr ⟨16, by decide⟩ 11 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 11 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_11.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_12 (hp : 12 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 12 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 12 (transLenTr ⟨16, by decide⟩ 12 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 12 (transLenTr ⟨16, by decide⟩ 12 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 12 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_12.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_13 (hp : 13 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 13 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 13 (transLenTr ⟨16, by decide⟩ 13 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 13 (transLenTr ⟨16, by decide⟩ 13 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 13 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_13.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_14 (hp : 14 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 14 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 14 (transLenTr ⟨16, by decide⟩ 14 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 14 (transLenTr ⟨16, by decide⟩ 14 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 14 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_14.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_15 (hp : 15 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 15 (transLenTr ⟨16, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 15 (transLenTr ⟨16, by decide⟩ 15 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 15 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_16 (hp : 16 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 16 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 16 (transLenTr ⟨16, by decide⟩ 16 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 16 (transLenTr ⟨16, by decide⟩ 16 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 16 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_16.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_17 (hp : 17 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 17 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 17 (transLenTr ⟨16, by decide⟩ 17 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 17 (transLenTr ⟨16, by decide⟩ 17 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 17 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_17.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_18 (hp : 18 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 18 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 18 (transLenTr ⟨16, by decide⟩ 18 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 18 (transLenTr ⟨16, by decide⟩ 18 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 18 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_18.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_19 (hp : 19 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 19 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 19 (transLenTr ⟨16, by decide⟩ 19 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 19 (transLenTr ⟨16, by decide⟩ 19 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 19 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_19.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_20 (hp : 20 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 20 (transLenTr ⟨16, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 20 (transLenTr ⟨16, by decide⟩ 20 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 20 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_21 (hp : 21 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 21 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 21 (transLenTr ⟨16, by decide⟩ 21 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 21 (transLenTr ⟨16, by decide⟩ 21 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 21 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_21.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_22 (hp : 22 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 22 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 22 (transLenTr ⟨16, by decide⟩ 22 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 22 (transLenTr ⟨16, by decide⟩ 22 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 22 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_22.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_23 (hp : 23 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 23 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 23 (transLenTr ⟨16, by decide⟩ 23 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 23 (transLenTr ⟨16, by decide⟩ 23 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 23 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_23.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_16_24 (hp : 24 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 24 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 24 (transLenTr ⟨16, by decide⟩ 24 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 24 (transLenTr ⟨16, by decide⟩ 24 hp)) T85_16
      hfix85_16 hinj85_16 hcardT85_16
      (fun i => conj_mem_of_fixedPoints _ _ (T85_16 i) (hfix85_16 i) _)
      ⟨85, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 24 hp) Q2.T85_16_2 Q2.hfix85_16_2 Q2.hinj85_16_2
      Q2.hcardT85_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_16_2 i) (Q2.hfix85_16_2 i) _)
      colCert_85_16_24.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_0 (hp : 0 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 0 (transLenTr ⟨17, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 0 (transLenTr ⟨17, by decide⟩ 0 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 0 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_1 (hp : 1 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 1 (transLenTr ⟨17, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 1 (transLenTr ⟨17, by decide⟩ 1 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 1 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_2 (hp : 2 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 2 (transLenTr ⟨17, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 2 (transLenTr ⟨17, by decide⟩ 2 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 2 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_3 (hp : 3 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 3 (transLenTr ⟨17, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 3 (transLenTr ⟨17, by decide⟩ 3 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 3 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_4 (hp : 4 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 4 (transLenTr ⟨17, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 4 (transLenTr ⟨17, by decide⟩ 4 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 4 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_5 (hp : 5 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 5 (transLenTr ⟨17, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 5 (transLenTr ⟨17, by decide⟩ 5 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 5 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_6 (hp : 6 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 6 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 6 (transLenTr ⟨17, by decide⟩ 6 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 6 (transLenTr ⟨17, by decide⟩ 6 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 6 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_6.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_7 (hp : 7 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 7 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 7 (transLenTr ⟨17, by decide⟩ 7 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 7 (transLenTr ⟨17, by decide⟩ 7 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 7 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_7.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_8 (hp : 8 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 8 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 8 (transLenTr ⟨17, by decide⟩ 8 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 8 (transLenTr ⟨17, by decide⟩ 8 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 8 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_8.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_9 (hp : 9 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 9 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 9 (transLenTr ⟨17, by decide⟩ 9 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 9 (transLenTr ⟨17, by decide⟩ 9 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 9 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_9.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_10 (hp : 10 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 10 (transLenTr ⟨17, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 10 (transLenTr ⟨17, by decide⟩ 10 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 10 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_11 (hp : 11 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 11 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 11 (transLenTr ⟨17, by decide⟩ 11 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 11 (transLenTr ⟨17, by decide⟩ 11 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 11 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_11.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_12 (hp : 12 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 12 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 12 (transLenTr ⟨17, by decide⟩ 12 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 12 (transLenTr ⟨17, by decide⟩ 12 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 12 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_12.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_13 (hp : 13 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 13 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 13 (transLenTr ⟨17, by decide⟩ 13 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 13 (transLenTr ⟨17, by decide⟩ 13 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 13 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_13.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_14 (hp : 14 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 14 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 14 (transLenTr ⟨17, by decide⟩ 14 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 14 (transLenTr ⟨17, by decide⟩ 14 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 14 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_14.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_15 (hp : 15 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 15 (transLenTr ⟨17, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 15 (transLenTr ⟨17, by decide⟩ 15 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 15 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_16 (hp : 16 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 16 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 16 (transLenTr ⟨17, by decide⟩ 16 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 16 (transLenTr ⟨17, by decide⟩ 16 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 16 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_16.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_17 (hp : 17 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 17 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 17 (transLenTr ⟨17, by decide⟩ 17 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 17 (transLenTr ⟨17, by decide⟩ 17 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 17 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_17.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_18 (hp : 18 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 18 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 18 (transLenTr ⟨17, by decide⟩ 18 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 18 (transLenTr ⟨17, by decide⟩ 18 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 18 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_18.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_19 (hp : 19 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 19 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 19 (transLenTr ⟨17, by decide⟩ 19 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 19 (transLenTr ⟨17, by decide⟩ 19 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 19 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_19.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_20 (hp : 20 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 20 (transLenTr ⟨17, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 20 (transLenTr ⟨17, by decide⟩ 20 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 20 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_21 (hp : 21 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 21 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 21 (transLenTr ⟨17, by decide⟩ 21 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 21 (transLenTr ⟨17, by decide⟩ 21 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 21 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_21.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_22 (hp : 22 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 22 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 22 (transLenTr ⟨17, by decide⟩ 22 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 22 (transLenTr ⟨17, by decide⟩ 22 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 22 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_22.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_23 (hp : 23 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 23 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 23 (transLenTr ⟨17, by decide⟩ 23 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 23 (transLenTr ⟨17, by decide⟩ 23 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 23 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_23.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_17_24 (hp : 24 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 24 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 24 (transLenTr ⟨17, by decide⟩ 24 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 24 (transLenTr ⟨17, by decide⟩ 24 hp)) T85_17
      hfix85_17 hinj85_17 hcardT85_17
      (fun i => conj_mem_of_fixedPoints _ _ (T85_17 i) (hfix85_17 i) _)
      ⟨85, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 24 hp) Q2.T85_17_2 Q2.hfix85_17_2 Q2.hinj85_17_2
      Q2.hcardT85_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_17_2 i) (Q2.hfix85_17_2 i) _)
      colCert_85_17_24.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_0 (hp : 0 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 0 (transLenTr ⟨18, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 0 (transLenTr ⟨18, by decide⟩ 0 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 0 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_1 (hp : 1 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 1 (transLenTr ⟨18, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 1 (transLenTr ⟨18, by decide⟩ 1 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 1 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_2 (hp : 2 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 2 (transLenTr ⟨18, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 2 (transLenTr ⟨18, by decide⟩ 2 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 2 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_3 (hp : 3 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 3 (transLenTr ⟨18, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 3 (transLenTr ⟨18, by decide⟩ 3 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 3 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_4 (hp : 4 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 4 (transLenTr ⟨18, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 4 (transLenTr ⟨18, by decide⟩ 4 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 4 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_5 (hp : 5 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 5 (transLenTr ⟨18, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 5 (transLenTr ⟨18, by decide⟩ 5 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 5 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_6 (hp : 6 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 6 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 6 (transLenTr ⟨18, by decide⟩ 6 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 6 (transLenTr ⟨18, by decide⟩ 6 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 6 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_6.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_7 (hp : 7 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 7 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 7 (transLenTr ⟨18, by decide⟩ 7 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 7 (transLenTr ⟨18, by decide⟩ 7 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 7 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_7.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_8 (hp : 8 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 8 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 8 (transLenTr ⟨18, by decide⟩ 8 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 8 (transLenTr ⟨18, by decide⟩ 8 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 8 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_8.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_9 (hp : 9 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 9 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 9 (transLenTr ⟨18, by decide⟩ 9 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 9 (transLenTr ⟨18, by decide⟩ 9 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 9 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_9.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_10 (hp : 10 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 10 (transLenTr ⟨18, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 10 (transLenTr ⟨18, by decide⟩ 10 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 10 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_11 (hp : 11 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 11 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 11 (transLenTr ⟨18, by decide⟩ 11 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 11 (transLenTr ⟨18, by decide⟩ 11 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 11 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_11.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_12 (hp : 12 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 12 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 12 (transLenTr ⟨18, by decide⟩ 12 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 12 (transLenTr ⟨18, by decide⟩ 12 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 12 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_12.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_13 (hp : 13 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 13 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 13 (transLenTr ⟨18, by decide⟩ 13 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 13 (transLenTr ⟨18, by decide⟩ 13 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 13 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_13.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_14 (hp : 14 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 14 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 14 (transLenTr ⟨18, by decide⟩ 14 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 14 (transLenTr ⟨18, by decide⟩ 14 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 14 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_14.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_15 (hp : 15 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 15 (transLenTr ⟨18, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 15 (transLenTr ⟨18, by decide⟩ 15 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 15 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_16 (hp : 16 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 16 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 16 (transLenTr ⟨18, by decide⟩ 16 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 16 (transLenTr ⟨18, by decide⟩ 16 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 16 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_16.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_17 (hp : 17 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 17 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 17 (transLenTr ⟨18, by decide⟩ 17 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 17 (transLenTr ⟨18, by decide⟩ 17 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 17 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_17.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_18 (hp : 18 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 18 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 18 (transLenTr ⟨18, by decide⟩ 18 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 18 (transLenTr ⟨18, by decide⟩ 18 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 18 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_18.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_19 (hp : 19 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 19 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 19 (transLenTr ⟨18, by decide⟩ 19 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 19 (transLenTr ⟨18, by decide⟩ 19 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 19 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_19.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_20 (hp : 20 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 20 (transLenTr ⟨18, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 20 (transLenTr ⟨18, by decide⟩ 20 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 20 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_21 (hp : 21 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 21 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 21 (transLenTr ⟨18, by decide⟩ 21 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 21 (transLenTr ⟨18, by decide⟩ 21 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 21 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_21.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_22 (hp : 22 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 22 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 22 (transLenTr ⟨18, by decide⟩ 22 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 22 (transLenTr ⟨18, by decide⟩ 22 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 22 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_22.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_23 (hp : 23 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 23 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 23 (transLenTr ⟨18, by decide⟩ 23 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 23 (transLenTr ⟨18, by decide⟩ 23 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 23 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_23.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_18_24 (hp : 24 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 24 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 24 (transLenTr ⟨18, by decide⟩ 24 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 24 (transLenTr ⟨18, by decide⟩ 24 hp)) T85_18
      hfix85_18 hinj85_18 hcardT85_18
      (fun i => conj_mem_of_fixedPoints _ _ (T85_18 i) (hfix85_18 i) _)
      ⟨85, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 24 hp) Q2.T85_18_2 Q2.hfix85_18_2 Q2.hinj85_18_2
      Q2.hcardT85_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_18_2 i) (Q2.hfix85_18_2 i) _)
      colCert_85_18_24.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T85_20
      hfix85_20 hinj85_20 hcardT85_20
      (fun i => conj_mem_of_fixedPoints _ _ (T85_20 i) (hfix85_20 i) _)
      ⟨85, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T85_20_2 Q2.hfix85_20_2 Q2.hinj85_20_2
      Q2.hcardT85_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_20_2 i) (Q2.hfix85_20_2 i) _)
      colCert_85_20_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T85_20
      hfix85_20 hinj85_20 hcardT85_20
      (fun i => conj_mem_of_fixedPoints _ _ (T85_20 i) (hfix85_20 i) _)
      ⟨85, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T85_20_2 Q2.hfix85_20_2 Q2.hinj85_20_2
      Q2.hcardT85_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_20_2 i) (Q2.hfix85_20_2 i) _)
      colCert_85_20_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T85_20
      hfix85_20 hinj85_20 hcardT85_20
      (fun i => conj_mem_of_fixedPoints _ _ (T85_20 i) (hfix85_20 i) _)
      ⟨85, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T85_20_2 Q2.hfix85_20_2 Q2.hinj85_20_2
      Q2.hcardT85_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_20_2 i) (Q2.hfix85_20_2 i) _)
      colCert_85_20_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T85_20
      hfix85_20 hinj85_20 hcardT85_20
      (fun i => conj_mem_of_fixedPoints _ _ (T85_20 i) (hfix85_20 i) _)
      ⟨85, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T85_20_2 Q2.hfix85_20_2 Q2.hinj85_20_2
      Q2.hcardT85_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_20_2 i) (Q2.hfix85_20_2 i) _)
      colCert_85_20_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T85_20
      hfix85_20 hinj85_20 hcardT85_20
      (fun i => conj_mem_of_fixedPoints _ _ (T85_20 i) (hfix85_20 i) _)
      ⟨85, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T85_20_2 Q2.hfix85_20_2 Q2.hinj85_20_2
      Q2.hcardT85_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_20_2 i) (Q2.hfix85_20_2 i) _)
      colCert_85_20_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T85_20
      hfix85_20 hinj85_20 hcardT85_20
      (fun i => conj_mem_of_fixedPoints _ _ (T85_20 i) (hfix85_20 i) _)
      ⟨85, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T85_20_2 Q2.hfix85_20_2 Q2.hinj85_20_2
      Q2.hcardT85_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_20_2 i) (Q2.hfix85_20_2 i) _)
      colCert_85_20_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T85_20
      hfix85_20 hinj85_20 hcardT85_20
      (fun i => conj_mem_of_fixedPoints _ _ (T85_20 i) (hfix85_20 i) _)
      ⟨85, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T85_20_2 Q2.hfix85_20_2 Q2.hinj85_20_2
      Q2.hcardT85_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_20_2 i) (Q2.hfix85_20_2 i) _)
      colCert_85_20_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T85_20
      hfix85_20 hinj85_20 hcardT85_20
      (fun i => conj_mem_of_fixedPoints _ _ (T85_20 i) (hfix85_20 i) _)
      ⟨85, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T85_20_2 Q2.hfix85_20_2 Q2.hinj85_20_2
      Q2.hcardT85_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_20_2 i) (Q2.hfix85_20_2 i) _)
      colCert_85_20_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T85_20
      hfix85_20 hinj85_20 hcardT85_20
      (fun i => conj_mem_of_fixedPoints _ _ (T85_20 i) (hfix85_20 i) _)
      ⟨85, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T85_20_2 Q2.hfix85_20_2 Q2.hinj85_20_2
      Q2.hcardT85_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_20_2 i) (Q2.hfix85_20_2 i) _)
      colCert_85_20_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T85_21
      hfix85_21 hinj85_21 hcardT85_21
      (fun i => conj_mem_of_fixedPoints _ _ (T85_21 i) (hfix85_21 i) _)
      ⟨85, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T85_21_2 Q2.hfix85_21_2 Q2.hinj85_21_2
      Q2.hcardT85_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_21_2 i) (Q2.hfix85_21_2 i) _)
      colCert_85_21_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T85_21
      hfix85_21 hinj85_21 hcardT85_21
      (fun i => conj_mem_of_fixedPoints _ _ (T85_21 i) (hfix85_21 i) _)
      ⟨85, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T85_21_2 Q2.hfix85_21_2 Q2.hinj85_21_2
      Q2.hcardT85_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_21_2 i) (Q2.hfix85_21_2 i) _)
      colCert_85_21_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T85_21
      hfix85_21 hinj85_21 hcardT85_21
      (fun i => conj_mem_of_fixedPoints _ _ (T85_21 i) (hfix85_21 i) _)
      ⟨85, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T85_21_2 Q2.hfix85_21_2 Q2.hinj85_21_2
      Q2.hcardT85_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_21_2 i) (Q2.hfix85_21_2 i) _)
      colCert_85_21_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T85_21
      hfix85_21 hinj85_21 hcardT85_21
      (fun i => conj_mem_of_fixedPoints _ _ (T85_21 i) (hfix85_21 i) _)
      ⟨85, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T85_21_2 Q2.hfix85_21_2 Q2.hinj85_21_2
      Q2.hcardT85_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_21_2 i) (Q2.hfix85_21_2 i) _)
      colCert_85_21_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T85_21
      hfix85_21 hinj85_21 hcardT85_21
      (fun i => conj_mem_of_fixedPoints _ _ (T85_21 i) (hfix85_21 i) _)
      ⟨85, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T85_21_2 Q2.hfix85_21_2 Q2.hinj85_21_2
      Q2.hcardT85_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_21_2 i) (Q2.hfix85_21_2 i) _)
      colCert_85_21_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T85_21
      hfix85_21 hinj85_21 hcardT85_21
      (fun i => conj_mem_of_fixedPoints _ _ (T85_21 i) (hfix85_21 i) _)
      ⟨85, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T85_21_2 Q2.hfix85_21_2 Q2.hinj85_21_2
      Q2.hcardT85_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_21_2 i) (Q2.hfix85_21_2 i) _)
      colCert_85_21_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T85_21
      hfix85_21 hinj85_21 hcardT85_21
      (fun i => conj_mem_of_fixedPoints _ _ (T85_21 i) (hfix85_21 i) _)
      ⟨85, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T85_21_2 Q2.hfix85_21_2 Q2.hinj85_21_2
      Q2.hcardT85_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_21_2 i) (Q2.hfix85_21_2 i) _)
      colCert_85_21_10.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T85_21
      hfix85_21 hinj85_21 hcardT85_21
      (fun i => conj_mem_of_fixedPoints _ _ (T85_21 i) (hfix85_21 i) _)
      ⟨85, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T85_21_2 Q2.hfix85_21_2 Q2.hinj85_21_2
      Q2.hcardT85_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_21_2 i) (Q2.hfix85_21_2 i) _)
      colCert_85_21_15.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T85_21
      hfix85_21 hinj85_21 hcardT85_21
      (fun i => conj_mem_of_fixedPoints _ _ (T85_21 i) (hfix85_21 i) _)
      ⟨85, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T85_21_2 Q2.hfix85_21_2 Q2.hinj85_21_2
      Q2.hcardT85_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_21_2 i) (Q2.hfix85_21_2 i) _)
      colCert_85_21_20.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T85_22
      hfix85_22 hinj85_22 hcardT85_22
      (fun i => conj_mem_of_fixedPoints _ _ (T85_22 i) (hfix85_22 i) _)
      ⟨85, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T85_22_2 Q2.hfix85_22_2 Q2.hinj85_22_2
      Q2.hcardT85_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_22_2 i) (Q2.hfix85_22_2 i) _)
      colCert_85_22_0.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T85_22
      hfix85_22 hinj85_22 hcardT85_22
      (fun i => conj_mem_of_fixedPoints _ _ (T85_22 i) (hfix85_22 i) _)
      ⟨85, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T85_22_2 Q2.hfix85_22_2 Q2.hinj85_22_2
      Q2.hcardT85_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_22_2 i) (Q2.hfix85_22_2 i) _)
      colCert_85_22_1.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T85_22
      hfix85_22 hinj85_22 hcardT85_22
      (fun i => conj_mem_of_fixedPoints _ _ (T85_22 i) (hfix85_22 i) _)
      ⟨85, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T85_22_2 Q2.hfix85_22_2 Q2.hinj85_22_2
      Q2.hcardT85_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_22_2 i) (Q2.hfix85_22_2 i) _)
      colCert_85_22_2.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T85_22
      hfix85_22 hinj85_22 hcardT85_22
      (fun i => conj_mem_of_fixedPoints _ _ (T85_22 i) (hfix85_22 i) _)
      ⟨85, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T85_22_2 Q2.hfix85_22_2 Q2.hinj85_22_2
      Q2.hcardT85_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_22_2 i) (Q2.hfix85_22_2 i) _)
      colCert_85_22_3.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T85_22
      hfix85_22 hinj85_22 hcardT85_22
      (fun i => conj_mem_of_fixedPoints _ _ (T85_22 i) (hfix85_22 i) _)
      ⟨85, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T85_22_2 Q2.hfix85_22_2 Q2.hinj85_22_2
      Q2.hcardT85_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_22_2 i) (Q2.hfix85_22_2 i) _)
      colCert_85_22_4.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T85_22
      hfix85_22 hinj85_22 hcardT85_22
      (fun i => conj_mem_of_fixedPoints _ _ (T85_22 i) (hfix85_22 i) _)
      ⟨85, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T85_22_2 Q2.hfix85_22_2 Q2.hinj85_22_2
      Q2.hcardT85_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_22_2 i) (Q2.hfix85_22_2 i) _)
      colCert_85_22_5.hD ?_).symm
  rw [alnId_85 j hj]


theorem leaf_85_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 85 []).length)
    (hq : (normIsRep.getD 85 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨85, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨85, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨85, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨85, by decide⟩ (listedAt ⟨85, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T85_22
      hfix85_22 hinj85_22 hcardT85_22
      (fun i => conj_mem_of_fixedPoints _ _ (T85_22 i) (hfix85_22 i) _)
      ⟨85, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨85, by decide⟩ (Q2.listedAt ⟨85, by decide⟩
        (alnCheck_rep ⟨85, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T85_22_2 Q2.hfix85_22_2 Q2.hinj85_22_2
      Q2.hcardT85_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T85_22_2 i) (Q2.hfix85_22_2 i) _)
      colCert_85_22_10.hD ?_).symm
  rw [alnId_85 j hj]


end LeanDring.P5Presentation
