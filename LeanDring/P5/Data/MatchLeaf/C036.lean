/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C013
import LeanDring.P5.Data.ColCdd.C014
import LeanDring.P5.Data.ColRestCheap.C064
import LeanDring.P5.Data.ColRestCheap.C065
import LeanDring.P5.Data.ColRestCheap.C066
import LeanDring.P5.Data.ColRestCheap.C067
import LeanDring.P5.Data.EntryK.C033
import LeanDring.P5.Data.EntryK.C034
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C015
import LeanDring.P5.Data.SpeciesDiv.C016
import LeanDring.P5.Data.SpeciesDiv.C017

/-! # Stage-5 leaves, chunk 35 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_129_82_2 (hp : 2 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp)) T129_82
      hfix129_82 hinj129_82 hcardT129_82
      (fun i => conj_mem_of_fixedPoints _ _ (T129_82 i) (hfix129_82 i) _)
      ⟨129, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 2 hp) Q2.T129_82_2 Q2.hfix129_82_2 Q2.hinj129_82_2
      Q2.hcardT129_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_82_2 i) (Q2.hfix129_82_2 i) _)
      colCert_129_82_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_82_3 (hp : 3 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp)) T129_82
      hfix129_82 hinj129_82 hcardT129_82
      (fun i => conj_mem_of_fixedPoints _ _ (T129_82 i) (hfix129_82 i) _)
      ⟨129, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 3 hp) Q2.T129_82_2 Q2.hfix129_82_2 Q2.hinj129_82_2
      Q2.hcardT129_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_82_2 i) (Q2.hfix129_82_2 i) _)
      colCert_129_82_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_82_4 (hp : 4 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp)) T129_82
      hfix129_82 hinj129_82 hcardT129_82
      (fun i => conj_mem_of_fixedPoints _ _ (T129_82 i) (hfix129_82 i) _)
      ⟨129, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 4 hp) Q2.T129_82_2 Q2.hfix129_82_2 Q2.hinj129_82_2
      Q2.hcardT129_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_82_2 i) (Q2.hfix129_82_2 i) _)
      colCert_129_82_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_82_5 (hp : 5 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp)) T129_82
      hfix129_82 hinj129_82 hcardT129_82
      (fun i => conj_mem_of_fixedPoints _ _ (T129_82 i) (hfix129_82 i) _)
      ⟨129, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 5 hp) Q2.T129_82_2 Q2.hfix129_82_2 Q2.hinj129_82_2
      Q2.hcardT129_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_82_2 i) (Q2.hfix129_82_2 i) _)
      colCert_129_82_5.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_82_10 (hp : 10 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp)) T129_82
      hfix129_82 hinj129_82 hcardT129_82
      (fun i => conj_mem_of_fixedPoints _ _ (T129_82 i) (hfix129_82 i) _)
      ⟨129, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 10 hp) Q2.T129_82_2 Q2.hfix129_82_2 Q2.hinj129_82_2
      Q2.hcardT129_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_82_2 i) (Q2.hfix129_82_2 i) _)
      colCert_129_82_10.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_82_15 (hp : 15 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp)) T129_82
      hfix129_82 hinj129_82 hcardT129_82
      (fun i => conj_mem_of_fixedPoints _ _ (T129_82 i) (hfix129_82 i) _)
      ⟨129, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 15 hp) Q2.T129_82_2 Q2.hfix129_82_2 Q2.hinj129_82_2
      Q2.hcardT129_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_82_2 i) (Q2.hfix129_82_2 i) _)
      colCert_129_82_15.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_82_20 (hp : 20 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp)) T129_82
      hfix129_82 hinj129_82 hcardT129_82
      (fun i => conj_mem_of_fixedPoints _ _ (T129_82 i) (hfix129_82 i) _)
      ⟨129, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 20 hp) Q2.T129_82_2 Q2.hfix129_82_2 Q2.hinj129_82_2
      Q2.hcardT129_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_82_2 i) (Q2.hfix129_82_2 i) _)
      colCert_129_82_20.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_91_0 (hp : 0 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp)) T129_91
      hfix129_91 hinj129_91 hcardT129_91
      (fun i => conj_mem_of_fixedPoints _ _ (T129_91 i) (hfix129_91 i) _)
      ⟨129, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 0 hp) Q2.T129_91_2 Q2.hfix129_91_2 Q2.hinj129_91_2
      Q2.hcardT129_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_91_2 i) (Q2.hfix129_91_2 i) _)
      colCert_129_91_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_91_1 (hp : 1 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp)) T129_91
      hfix129_91 hinj129_91 hcardT129_91
      (fun i => conj_mem_of_fixedPoints _ _ (T129_91 i) (hfix129_91 i) _)
      ⟨129, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 1 hp) Q2.T129_91_2 Q2.hfix129_91_2 Q2.hinj129_91_2
      Q2.hcardT129_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_91_2 i) (Q2.hfix129_91_2 i) _)
      colCert_129_91_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_91_2 (hp : 2 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp)) T129_91
      hfix129_91 hinj129_91 hcardT129_91
      (fun i => conj_mem_of_fixedPoints _ _ (T129_91 i) (hfix129_91 i) _)
      ⟨129, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 2 hp) Q2.T129_91_2 Q2.hfix129_91_2 Q2.hinj129_91_2
      Q2.hcardT129_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_91_2 i) (Q2.hfix129_91_2 i) _)
      colCert_129_91_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_91_3 (hp : 3 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp)) T129_91
      hfix129_91 hinj129_91 hcardT129_91
      (fun i => conj_mem_of_fixedPoints _ _ (T129_91 i) (hfix129_91 i) _)
      ⟨129, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 3 hp) Q2.T129_91_2 Q2.hfix129_91_2 Q2.hinj129_91_2
      Q2.hcardT129_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_91_2 i) (Q2.hfix129_91_2 i) _)
      colCert_129_91_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_91_4 (hp : 4 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp)) T129_91
      hfix129_91 hinj129_91 hcardT129_91
      (fun i => conj_mem_of_fixedPoints _ _ (T129_91 i) (hfix129_91 i) _)
      ⟨129, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 4 hp) Q2.T129_91_2 Q2.hfix129_91_2 Q2.hinj129_91_2
      Q2.hcardT129_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_91_2 i) (Q2.hfix129_91_2 i) _)
      colCert_129_91_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_91_5 (hp : 5 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp)) T129_91
      hfix129_91 hinj129_91 hcardT129_91
      (fun i => conj_mem_of_fixedPoints _ _ (T129_91 i) (hfix129_91 i) _)
      ⟨129, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 5 hp) Q2.T129_91_2 Q2.hfix129_91_2 Q2.hinj129_91_2
      Q2.hcardT129_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_91_2 i) (Q2.hfix129_91_2 i) _)
      colCert_129_91_5.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_91_10 (hp : 10 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp)) T129_91
      hfix129_91 hinj129_91 hcardT129_91
      (fun i => conj_mem_of_fixedPoints _ _ (T129_91 i) (hfix129_91 i) _)
      ⟨129, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 10 hp) Q2.T129_91_2 Q2.hfix129_91_2 Q2.hinj129_91_2
      Q2.hcardT129_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_91_2 i) (Q2.hfix129_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T129_91 = colFn colCertDiv_129_91_10.D1 (m := 5) from colCertDiv_129_91_10.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 10 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T129_91_2 = colFn colCertDiv_129_91_10.D2 (m := 5) from colCertDiv_129_91_10.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_91_10_match


theorem leaf_129_91_15 (hp : 15 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp)) T129_91
      hfix129_91 hinj129_91 hcardT129_91
      (fun i => conj_mem_of_fixedPoints _ _ (T129_91 i) (hfix129_91 i) _)
      ⟨129, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 15 hp) Q2.T129_91_2 Q2.hfix129_91_2 Q2.hinj129_91_2
      Q2.hcardT129_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_91_2 i) (Q2.hfix129_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T129_91 = colFn colCertDiv_129_91_15.D1 (m := 5) from colCertDiv_129_91_15.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 15 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T129_91_2 = colFn colCertDiv_129_91_15.D2 (m := 5) from colCertDiv_129_91_15.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_91_15_match


theorem leaf_129_91_20 (hp : 20 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp)) T129_91
      hfix129_91 hinj129_91 hcardT129_91
      (fun i => conj_mem_of_fixedPoints _ _ (T129_91 i) (hfix129_91 i) _)
      ⟨129, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 20 hp) Q2.T129_91_2 Q2.hfix129_91_2 Q2.hinj129_91_2
      Q2.hcardT129_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_91_2 i) (Q2.hfix129_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T129_91 = colFn colCertDiv_129_91_20.D1 (m := 5) from colCertDiv_129_91_20.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 20 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T129_91_2 = colFn colCertDiv_129_91_20.D2 (m := 5) from colCertDiv_129_91_20.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_91_20_match


theorem leaf_129_97_0 (hp : 0 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 0 (transLenTr ⟨97, by decide⟩ 0 hp)) T129_97
      hfix129_97 hinj129_97 hcardT129_97
      (fun i => conj_mem_of_fixedPoints _ _ (T129_97 i) (hfix129_97 i) _)
      ⟨129, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 0 hp) Q2.T129_97_2 Q2.hfix129_97_2 Q2.hinj129_97_2
      Q2.hcardT129_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_97_2 i) (Q2.hfix129_97_2 i) _)
      colCert_129_97_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_97_1 (hp : 1 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 1 (transLenTr ⟨97, by decide⟩ 1 hp)) T129_97
      hfix129_97 hinj129_97 hcardT129_97
      (fun i => conj_mem_of_fixedPoints _ _ (T129_97 i) (hfix129_97 i) _)
      ⟨129, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 1 hp) Q2.T129_97_2 Q2.hfix129_97_2 Q2.hinj129_97_2
      Q2.hcardT129_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_97_2 i) (Q2.hfix129_97_2 i) _)
      colCert_129_97_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_97_2 (hp : 2 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 2 (transLenTr ⟨97, by decide⟩ 2 hp)) T129_97
      hfix129_97 hinj129_97 hcardT129_97
      (fun i => conj_mem_of_fixedPoints _ _ (T129_97 i) (hfix129_97 i) _)
      ⟨129, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 2 hp) Q2.T129_97_2 Q2.hfix129_97_2 Q2.hinj129_97_2
      Q2.hcardT129_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_97_2 i) (Q2.hfix129_97_2 i) _)
      colCert_129_97_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_97_3 (hp : 3 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 3 (transLenTr ⟨97, by decide⟩ 3 hp)) T129_97
      hfix129_97 hinj129_97 hcardT129_97
      (fun i => conj_mem_of_fixedPoints _ _ (T129_97 i) (hfix129_97 i) _)
      ⟨129, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 3 hp) Q2.T129_97_2 Q2.hfix129_97_2 Q2.hinj129_97_2
      Q2.hcardT129_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_97_2 i) (Q2.hfix129_97_2 i) _)
      colCert_129_97_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_97_4 (hp : 4 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 4 (transLenTr ⟨97, by decide⟩ 4 hp)) T129_97
      hfix129_97 hinj129_97 hcardT129_97
      (fun i => conj_mem_of_fixedPoints _ _ (T129_97 i) (hfix129_97 i) _)
      ⟨129, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 4 hp) Q2.T129_97_2 Q2.hfix129_97_2 Q2.hinj129_97_2
      Q2.hcardT129_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_97_2 i) (Q2.hfix129_97_2 i) _)
      colCert_129_97_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_97_5 (hp : 5 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 5 (transLenTr ⟨97, by decide⟩ 5 hp)) T129_97
      hfix129_97 hinj129_97 hcardT129_97
      (fun i => conj_mem_of_fixedPoints _ _ (T129_97 i) (hfix129_97 i) _)
      ⟨129, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 5 hp) Q2.T129_97_2 Q2.hfix129_97_2 Q2.hinj129_97_2
      Q2.hcardT129_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_97_2 i) (Q2.hfix129_97_2 i) _)
      colCert_129_97_5.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_97_10 (hp : 10 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 10 (transLenTr ⟨97, by decide⟩ 10 hp)) T129_97
      hfix129_97 hinj129_97 hcardT129_97
      (fun i => conj_mem_of_fixedPoints _ _ (T129_97 i) (hfix129_97 i) _)
      ⟨129, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 10 hp) Q2.T129_97_2 Q2.hfix129_97_2 Q2.hinj129_97_2
      Q2.hcardT129_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_97_2 i) (Q2.hfix129_97_2 i) _)
      colCert_129_97_10.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_97_15 (hp : 15 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp)) T129_97
      hfix129_97 hinj129_97 hcardT129_97
      (fun i => conj_mem_of_fixedPoints _ _ (T129_97 i) (hfix129_97 i) _)
      ⟨129, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 15 hp) Q2.T129_97_2 Q2.hfix129_97_2 Q2.hinj129_97_2
      Q2.hcardT129_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_97_2 i) (Q2.hfix129_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 15 (transLenTr ⟨97, by decide⟩ 15 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T129_97 = colFn colCertDiv_129_97_15.D1 (m := 5) from colCertDiv_129_97_15.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 15 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T129_97_2 = colFn colCertDiv_129_97_15.D2 (m := 5) from colCertDiv_129_97_15.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_97_15_match


theorem leaf_129_97_20 (hp : 20 < (Q2.transData.getD 97 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨97, by decide⟩ : Fin 148)) (colE2 ⟨97, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨97, by decide⟩ : Fin 148))
        (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨97, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp)) T129_97
      hfix129_97 hinj129_97 hcardT129_97
      (fun i => conj_mem_of_fixedPoints _ _ (T129_97 i) (hfix129_97 i) _)
      ⟨129, by decide⟩ ⟨97, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨97, by decide⟩ 20 hp) Q2.T129_97_2 Q2.hfix129_97_2 Q2.hinj129_97_2
      Q2.hcardT129_97_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_97_2 i) (Q2.hfix129_97_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨97, by decide⟩ 20 (transLenTr ⟨97, by decide⟩ 20 hp) : ↥(reps ⟨97, by decide⟩)) : Coordinate 1)
        T129_97 = colFn colCertDiv_129_97_20.D1 (m := 5) from colCertDiv_129_97_20.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨97, by decide⟩ 20 hp : ↥(Q2.reps ⟨97, by decide⟩)) : Coordinate 2)
        Q2.T129_97_2 = colFn colCertDiv_129_97_20.D2 (m := 5) from colCertDiv_129_97_20.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_97_20_match


theorem leaf_129_104_0 (hp : 0 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 0 (transLenTr ⟨104, by decide⟩ 0 hp)) T129_104
      hfix129_104 hinj129_104 hcardT129_104
      (fun i => conj_mem_of_fixedPoints _ _ (T129_104 i) (hfix129_104 i) _)
      ⟨129, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 0 hp) Q2.T129_104_2 Q2.hfix129_104_2 Q2.hinj129_104_2
      Q2.hcardT129_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_104_2 i) (Q2.hfix129_104_2 i) _)
      colCert_129_104_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_104_1 (hp : 1 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 1 (transLenTr ⟨104, by decide⟩ 1 hp)) T129_104
      hfix129_104 hinj129_104 hcardT129_104
      (fun i => conj_mem_of_fixedPoints _ _ (T129_104 i) (hfix129_104 i) _)
      ⟨129, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 1 hp) Q2.T129_104_2 Q2.hfix129_104_2 Q2.hinj129_104_2
      Q2.hcardT129_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_104_2 i) (Q2.hfix129_104_2 i) _)
      colCert_129_104_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_104_2 (hp : 2 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 2 (transLenTr ⟨104, by decide⟩ 2 hp)) T129_104
      hfix129_104 hinj129_104 hcardT129_104
      (fun i => conj_mem_of_fixedPoints _ _ (T129_104 i) (hfix129_104 i) _)
      ⟨129, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 2 hp) Q2.T129_104_2 Q2.hfix129_104_2 Q2.hinj129_104_2
      Q2.hcardT129_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_104_2 i) (Q2.hfix129_104_2 i) _)
      colCert_129_104_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_104_3 (hp : 3 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 3 (transLenTr ⟨104, by decide⟩ 3 hp)) T129_104
      hfix129_104 hinj129_104 hcardT129_104
      (fun i => conj_mem_of_fixedPoints _ _ (T129_104 i) (hfix129_104 i) _)
      ⟨129, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 3 hp) Q2.T129_104_2 Q2.hfix129_104_2 Q2.hinj129_104_2
      Q2.hcardT129_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_104_2 i) (Q2.hfix129_104_2 i) _)
      colCert_129_104_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_104_4 (hp : 4 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 4 (transLenTr ⟨104, by decide⟩ 4 hp)) T129_104
      hfix129_104 hinj129_104 hcardT129_104
      (fun i => conj_mem_of_fixedPoints _ _ (T129_104 i) (hfix129_104 i) _)
      ⟨129, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 4 hp) Q2.T129_104_2 Q2.hfix129_104_2 Q2.hinj129_104_2
      Q2.hcardT129_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_104_2 i) (Q2.hfix129_104_2 i) _)
      colCert_129_104_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_104_5 (hp : 5 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 5 (transLenTr ⟨104, by decide⟩ 5 hp)) T129_104
      hfix129_104 hinj129_104 hcardT129_104
      (fun i => conj_mem_of_fixedPoints _ _ (T129_104 i) (hfix129_104 i) _)
      ⟨129, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 5 hp) Q2.T129_104_2 Q2.hfix129_104_2 Q2.hinj129_104_2
      Q2.hcardT129_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_104_2 i) (Q2.hfix129_104_2 i) _)
      colCert_129_104_5.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_104_10 (hp : 10 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 10 (transLenTr ⟨104, by decide⟩ 10 hp)) T129_104
      hfix129_104 hinj129_104 hcardT129_104
      (fun i => conj_mem_of_fixedPoints _ _ (T129_104 i) (hfix129_104 i) _)
      ⟨129, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 10 hp) Q2.T129_104_2 Q2.hfix129_104_2 Q2.hinj129_104_2
      Q2.hcardT129_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_104_2 i) (Q2.hfix129_104_2 i) _)
      colCert_129_104_10.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_104_15 (hp : 15 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 15 (transLenTr ⟨104, by decide⟩ 15 hp)) T129_104
      hfix129_104 hinj129_104 hcardT129_104
      (fun i => conj_mem_of_fixedPoints _ _ (T129_104 i) (hfix129_104 i) _)
      ⟨129, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 15 hp) Q2.T129_104_2 Q2.hfix129_104_2 Q2.hinj129_104_2
      Q2.hcardT129_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_104_2 i) (Q2.hfix129_104_2 i) _)
      colCert_129_104_15.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_104_20 (hp : 20 < (Q2.transData.getD 104 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨104, by decide⟩ : Fin 148)) (colE2 ⟨104, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨104, by decide⟩ : Fin 148))
        (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨104, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨104, by decide⟩ 20 (transLenTr ⟨104, by decide⟩ 20 hp)) T129_104
      hfix129_104 hinj129_104 hcardT129_104
      (fun i => conj_mem_of_fixedPoints _ _ (T129_104 i) (hfix129_104 i) _)
      ⟨129, by decide⟩ ⟨104, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨104, by decide⟩ 20 hp) Q2.T129_104_2 Q2.hfix129_104_2 Q2.hinj129_104_2
      Q2.hcardT129_104_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_104_2 i) (Q2.hfix129_104_2 i) _)
      colCert_129_104_20.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_0 (hp : 0 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 0 (transLenTr ⟨105, by decide⟩ 0 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 0 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_1 (hp : 1 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 1 (transLenTr ⟨105, by decide⟩ 1 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 1 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_2 (hp : 2 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 2 (transLenTr ⟨105, by decide⟩ 2 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 2 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_3 (hp : 3 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 3 (transLenTr ⟨105, by decide⟩ 3 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 3 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_4 (hp : 4 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 4 (transLenTr ⟨105, by decide⟩ 4 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 4 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_5 (hp : 5 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 5 (transLenTr ⟨105, by decide⟩ 5 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 5 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_5.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_10 (hp : 10 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 10 (transLenTr ⟨105, by decide⟩ 10 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 10 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_10.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_15 (hp : 15 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 15 (transLenTr ⟨105, by decide⟩ 15 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 15 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_15.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_20 (hp : 20 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 20 (transLenTr ⟨105, by decide⟩ 20 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 20 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_20.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_25 (hp : 25 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 25 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 25 (transLenTr ⟨105, by decide⟩ 25 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 25 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_25.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_50 (hp : 50 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 50 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 50 (transLenTr ⟨105, by decide⟩ 50 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 50 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_50.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_75 (hp : 75 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 75 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 75 (transLenTr ⟨105, by decide⟩ 75 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 75 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_75.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_105_100 (hp : 100 < (Q2.transData.getD 105 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨105, by decide⟩ : Fin 148)) (colE2 ⟨105, by decide⟩ 100 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨105, by decide⟩ : Fin 148))
        (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨105, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨105, by decide⟩ 100 (transLenTr ⟨105, by decide⟩ 100 hp)) T129_105
      hfix129_105 hinj129_105 hcardT129_105
      (fun i => conj_mem_of_fixedPoints _ _ (T129_105 i) (hfix129_105 i) _)
      ⟨129, by decide⟩ ⟨105, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨105, by decide⟩ 100 hp) Q2.T129_105_2 Q2.hfix129_105_2 Q2.hinj129_105_2
      Q2.hcardT129_105_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_105_2 i) (Q2.hfix129_105_2 i) _)
      colCert_129_105_100.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_113_0 (hp : 0 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp)) T129_113
      hfix129_113 hinj129_113 hcardT129_113
      (fun i => conj_mem_of_fixedPoints _ _ (T129_113 i) (hfix129_113 i) _)
      ⟨129, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 0 hp) Q2.T129_113_2 Q2.hfix129_113_2 Q2.hinj129_113_2
      Q2.hcardT129_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_113_2 i) (Q2.hfix129_113_2 i) _)
      colCert_129_113_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_113_1 (hp : 1 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp)) T129_113
      hfix129_113 hinj129_113 hcardT129_113
      (fun i => conj_mem_of_fixedPoints _ _ (T129_113 i) (hfix129_113 i) _)
      ⟨129, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 1 hp) Q2.T129_113_2 Q2.hfix129_113_2 Q2.hinj129_113_2
      Q2.hcardT129_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_113_2 i) (Q2.hfix129_113_2 i) _)
      colCert_129_113_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_113_2 (hp : 2 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp)) T129_113
      hfix129_113 hinj129_113 hcardT129_113
      (fun i => conj_mem_of_fixedPoints _ _ (T129_113 i) (hfix129_113 i) _)
      ⟨129, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 2 hp) Q2.T129_113_2 Q2.hfix129_113_2 Q2.hinj129_113_2
      Q2.hcardT129_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_113_2 i) (Q2.hfix129_113_2 i) _)
      colCert_129_113_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_113_3 (hp : 3 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp)) T129_113
      hfix129_113 hinj129_113 hcardT129_113
      (fun i => conj_mem_of_fixedPoints _ _ (T129_113 i) (hfix129_113 i) _)
      ⟨129, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 3 hp) Q2.T129_113_2 Q2.hfix129_113_2 Q2.hinj129_113_2
      Q2.hcardT129_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_113_2 i) (Q2.hfix129_113_2 i) _)
      colCert_129_113_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_113_4 (hp : 4 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp)) T129_113
      hfix129_113 hinj129_113 hcardT129_113
      (fun i => conj_mem_of_fixedPoints _ _ (T129_113 i) (hfix129_113 i) _)
      ⟨129, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 4 hp) Q2.T129_113_2 Q2.hfix129_113_2 Q2.hinj129_113_2
      Q2.hcardT129_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_113_2 i) (Q2.hfix129_113_2 i) _)
      colCert_129_113_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_113_5 (hp : 5 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp)) T129_113
      hfix129_113 hinj129_113 hcardT129_113
      (fun i => conj_mem_of_fixedPoints _ _ (T129_113 i) (hfix129_113 i) _)
      ⟨129, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 5 hp) Q2.T129_113_2 Q2.hfix129_113_2 Q2.hinj129_113_2
      Q2.hcardT129_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_113_2 i) (Q2.hfix129_113_2 i) _)
      colCert_129_113_5.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_113_10 (hp : 10 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp)) T129_113
      hfix129_113 hinj129_113 hcardT129_113
      (fun i => conj_mem_of_fixedPoints _ _ (T129_113 i) (hfix129_113 i) _)
      ⟨129, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 10 hp) Q2.T129_113_2 Q2.hfix129_113_2 Q2.hinj129_113_2
      Q2.hcardT129_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_113_2 i) (Q2.hfix129_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T129_113 = colFn colCertDiv_129_113_10.D1 (m := 5) from colCertDiv_129_113_10.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 10 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T129_113_2 = colFn colCertDiv_129_113_10.D2 (m := 5) from colCertDiv_129_113_10.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_113_10_match


theorem leaf_129_113_15 (hp : 15 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp)) T129_113
      hfix129_113 hinj129_113 hcardT129_113
      (fun i => conj_mem_of_fixedPoints _ _ (T129_113 i) (hfix129_113 i) _)
      ⟨129, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 15 hp) Q2.T129_113_2 Q2.hfix129_113_2 Q2.hinj129_113_2
      Q2.hcardT129_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_113_2 i) (Q2.hfix129_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T129_113 = colFn colCertDiv_129_113_15.D1 (m := 5) from colCertDiv_129_113_15.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 15 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T129_113_2 = colFn colCertDiv_129_113_15.D2 (m := 5) from colCertDiv_129_113_15.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_113_15_match


theorem leaf_129_113_20 (hp : 20 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨129, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp)) T129_113
      hfix129_113 hinj129_113 hcardT129_113
      (fun i => conj_mem_of_fixedPoints _ _ (T129_113 i) (hfix129_113 i) _)
      ⟨129, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 20 hp) Q2.T129_113_2 Q2.hfix129_113_2 Q2.hinj129_113_2
      Q2.hcardT129_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_113_2 i) (Q2.hfix129_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨129, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T129_113 = colFn colCertDiv_129_113_20.D1 (m := 5) from colCertDiv_129_113_20.bind1,
    show colData2 (⟨129, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 20 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T129_113_2 = colFn colCertDiv_129_113_20.D2 (m := 5) from colCertDiv_129_113_20.bind2]
  rw [alnId_129 j hj]
  exact fastcode_of_div ⟨129, by decide⟩ _ _ _
    ((alnId_129 j hj) ▸ Q2.listedAt (⟨129, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨129, by decide⟩ : Fin 148) hj hq).1) colCertDiv_129_113_20_match


theorem leaf_129_129_0 (hp : 0 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 0 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 0 (transLenTr ⟨129, by decide⟩ 0 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 0 (transLenTr ⟨129, by decide⟩ 0 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 0 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_0.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_1 (hp : 1 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 1 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 1 (transLenTr ⟨129, by decide⟩ 1 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 1 (transLenTr ⟨129, by decide⟩ 1 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 1 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_1.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_2 (hp : 2 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 2 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 2 (transLenTr ⟨129, by decide⟩ 2 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 2 (transLenTr ⟨129, by decide⟩ 2 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 2 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_2.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_3 (hp : 3 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 3 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 3 (transLenTr ⟨129, by decide⟩ 3 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 3 (transLenTr ⟨129, by decide⟩ 3 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 3 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_3.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_4 (hp : 4 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 4 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 4 (transLenTr ⟨129, by decide⟩ 4 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 4 (transLenTr ⟨129, by decide⟩ 4 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 4 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_4.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_5 (hp : 5 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 5 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 5 (transLenTr ⟨129, by decide⟩ 5 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 5 (transLenTr ⟨129, by decide⟩ 5 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 5 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_5.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_6 (hp : 6 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 6 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 6 (transLenTr ⟨129, by decide⟩ 6 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 6 (transLenTr ⟨129, by decide⟩ 6 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 6 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_6.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_7 (hp : 7 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 7 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 7 (transLenTr ⟨129, by decide⟩ 7 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 7 (transLenTr ⟨129, by decide⟩ 7 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 7 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_7.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_8 (hp : 8 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 8 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 8 (transLenTr ⟨129, by decide⟩ 8 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 8 (transLenTr ⟨129, by decide⟩ 8 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 8 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_8.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_9 (hp : 9 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 9 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 9 (transLenTr ⟨129, by decide⟩ 9 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 9 (transLenTr ⟨129, by decide⟩ 9 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 9 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_9.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_10 (hp : 10 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 10 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 10 (transLenTr ⟨129, by decide⟩ 10 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 10 (transLenTr ⟨129, by decide⟩ 10 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 10 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_10.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_11 (hp : 11 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 11 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 11 (transLenTr ⟨129, by decide⟩ 11 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 11 (transLenTr ⟨129, by decide⟩ 11 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 11 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_11.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_12 (hp : 12 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 12 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 12 (transLenTr ⟨129, by decide⟩ 12 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 12 (transLenTr ⟨129, by decide⟩ 12 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 12 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_12.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_13 (hp : 13 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 13 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 13 (transLenTr ⟨129, by decide⟩ 13 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 13 (transLenTr ⟨129, by decide⟩ 13 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 13 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_13.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_14 (hp : 14 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 14 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 14 (transLenTr ⟨129, by decide⟩ 14 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 14 (transLenTr ⟨129, by decide⟩ 14 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 14 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_14.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_15 (hp : 15 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 15 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 15 (transLenTr ⟨129, by decide⟩ 15 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 15 (transLenTr ⟨129, by decide⟩ 15 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 15 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_15.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_16 (hp : 16 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 16 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 16 (transLenTr ⟨129, by decide⟩ 16 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 16 (transLenTr ⟨129, by decide⟩ 16 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 16 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_16.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_17 (hp : 17 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 17 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 17 (transLenTr ⟨129, by decide⟩ 17 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 17 (transLenTr ⟨129, by decide⟩ 17 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 17 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_17.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_18 (hp : 18 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 18 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 18 (transLenTr ⟨129, by decide⟩ 18 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 18 (transLenTr ⟨129, by decide⟩ 18 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 18 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_18.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_19 (hp : 19 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 19 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 19 (transLenTr ⟨129, by decide⟩ 19 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 19 (transLenTr ⟨129, by decide⟩ 19 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 19 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_19.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_20 (hp : 20 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 20 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 20 (transLenTr ⟨129, by decide⟩ 20 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 20 (transLenTr ⟨129, by decide⟩ 20 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 20 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_20.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_21 (hp : 21 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 21 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 21 (transLenTr ⟨129, by decide⟩ 21 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 21 (transLenTr ⟨129, by decide⟩ 21 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 21 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_21.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_22 (hp : 22 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 22 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 22 (transLenTr ⟨129, by decide⟩ 22 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 22 (transLenTr ⟨129, by decide⟩ 22 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 22 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_22.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_23 (hp : 23 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 23 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 23 (transLenTr ⟨129, by decide⟩ 23 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 23 (transLenTr ⟨129, by decide⟩ 23 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 23 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_23.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_129_129_24 (hp : 24 < (Q2.transData.getD 129 []).length)
    (j : Nat) (hj : j < (repChars.getD 129 []).length)
    (hq : (normIsRep.getD 129 []).getD j false = true) :
    species (Q2.reps (⟨129, by decide⟩ : Fin 148)) (colE2 ⟨129, by decide⟩ 24 hp)
        (rowE2 (⟨129, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨129, by decide⟩ : Fin 148))
        (colE1 ⟨129, by decide⟩ 24 (transLenTr ⟨129, by decide⟩ 24 hp))
        (rowE1 (⟨129, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨129, by decide⟩ : Fin 148) ⟨129, by decide⟩ _
      (validAt ⟨129, by decide⟩ (listedAt ⟨129, by decide⟩ hj))
      (colE1 ⟨129, by decide⟩ 24 (transLenTr ⟨129, by decide⟩ 24 hp)) T129_129
      hfix129_129 hinj129_129 hcardT129_129
      (fun i => conj_mem_of_fixedPoints _ _ (T129_129 i) (hfix129_129 i) _)
      ⟨129, by decide⟩ ⟨129, by decide⟩ _
      (Q2.validAt ⟨129, by decide⟩ (Q2.listedAt ⟨129, by decide⟩
        (alnCheck_rep ⟨129, by decide⟩ hj hq).1))
      (colE2 ⟨129, by decide⟩ 24 hp) Q2.T129_129_2 Q2.hfix129_129_2 Q2.hinj129_129_2
      Q2.hcardT129_129_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T129_129_2 i) (Q2.hfix129_129_2 i) _)
      colCert_129_129_24.hD ?_).symm
  rw [alnId_129 j hj]


theorem leaf_130_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T130_3
      hfix130_3 hinj130_3 hcardT130_3
      (fun i => conj_mem_of_fixedPoints _ _ (T130_3 i) (hfix130_3 i) _)
      ⟨130, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T130_3_2 Q2.hfix130_3_2 Q2.hinj130_3_2
      Q2.hcardT130_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_3_2 i) (Q2.hfix130_3_2 i) _)
      colCert_130_3_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T130_3
      hfix130_3 hinj130_3 hcardT130_3
      (fun i => conj_mem_of_fixedPoints _ _ (T130_3 i) (hfix130_3 i) _)
      ⟨130, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T130_3_2 Q2.hfix130_3_2 Q2.hinj130_3_2
      Q2.hcardT130_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_3_2 i) (Q2.hfix130_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T130_3 = colFn colCertDiv_130_3_1.D1 (m := 5) from colCertDiv_130_3_1.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 1 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T130_3_2 = colFn colCertDiv_130_3_1.D2 (m := 5) from colCertDiv_130_3_1.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_3_1_match


theorem leaf_130_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T130_3
      hfix130_3 hinj130_3 hcardT130_3
      (fun i => conj_mem_of_fixedPoints _ _ (T130_3 i) (hfix130_3 i) _)
      ⟨130, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T130_3_2 Q2.hfix130_3_2 Q2.hinj130_3_2
      Q2.hcardT130_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_3_2 i) (Q2.hfix130_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T130_3 = colFn colCertDiv_130_3_2.D1 (m := 5) from colCertDiv_130_3_2.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 2 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T130_3_2 = colFn colCertDiv_130_3_2.D2 (m := 5) from colCertDiv_130_3_2.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_3_2_match


theorem leaf_130_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T130_3
      hfix130_3 hinj130_3 hcardT130_3
      (fun i => conj_mem_of_fixedPoints _ _ (T130_3 i) (hfix130_3 i) _)
      ⟨130, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T130_3_2 Q2.hfix130_3_2 Q2.hinj130_3_2
      Q2.hcardT130_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_3_2 i) (Q2.hfix130_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T130_3 = colFn colCertDiv_130_3_3.D1 (m := 5) from colCertDiv_130_3_3.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 3 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T130_3_2 = colFn colCertDiv_130_3_3.D2 (m := 5) from colCertDiv_130_3_3.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_3_3_match


theorem leaf_130_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T130_3
      hfix130_3 hinj130_3 hcardT130_3
      (fun i => conj_mem_of_fixedPoints _ _ (T130_3 i) (hfix130_3 i) _)
      ⟨130, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T130_3_2 Q2.hfix130_3_2 Q2.hinj130_3_2
      Q2.hcardT130_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_3_2 i) (Q2.hfix130_3_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp) : ↥(reps ⟨3, by decide⟩)) : Coordinate 1)
        T130_3 = colFn colCertDiv_130_3_4.D1 (m := 5) from colCertDiv_130_3_4.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨3, by decide⟩ 4 hp : ↥(Q2.reps ⟨3, by decide⟩)) : Coordinate 2)
        Q2.T130_3_2 = colFn colCertDiv_130_3_4.D2 (m := 5) from colCertDiv_130_3_4.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_3_4_match


theorem leaf_130_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T130_10
      hfix130_10 hinj130_10 hcardT130_10
      (fun i => conj_mem_of_fixedPoints _ _ (T130_10 i) (hfix130_10 i) _)
      ⟨130, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T130_10_2 Q2.hfix130_10_2 Q2.hinj130_10_2
      Q2.hcardT130_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_10_2 i) (Q2.hfix130_10_2 i) _)
      colCert_130_10_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T130_10
      hfix130_10 hinj130_10 hcardT130_10
      (fun i => conj_mem_of_fixedPoints _ _ (T130_10 i) (hfix130_10 i) _)
      ⟨130, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T130_10_2 Q2.hfix130_10_2 Q2.hinj130_10_2
      Q2.hcardT130_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_10_2 i) (Q2.hfix130_10_2 i) _)
      colCert_130_10_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T130_10
      hfix130_10 hinj130_10 hcardT130_10
      (fun i => conj_mem_of_fixedPoints _ _ (T130_10 i) (hfix130_10 i) _)
      ⟨130, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T130_10_2 Q2.hfix130_10_2 Q2.hinj130_10_2
      Q2.hcardT130_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_10_2 i) (Q2.hfix130_10_2 i) _)
      colCert_130_10_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T130_10
      hfix130_10 hinj130_10 hcardT130_10
      (fun i => conj_mem_of_fixedPoints _ _ (T130_10 i) (hfix130_10 i) _)
      ⟨130, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T130_10_2 Q2.hfix130_10_2 Q2.hinj130_10_2
      Q2.hcardT130_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_10_2 i) (Q2.hfix130_10_2 i) _)
      colCert_130_10_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T130_10
      hfix130_10 hinj130_10 hcardT130_10
      (fun i => conj_mem_of_fixedPoints _ _ (T130_10 i) (hfix130_10 i) _)
      ⟨130, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T130_10_2 Q2.hfix130_10_2 Q2.hinj130_10_2
      Q2.hcardT130_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_10_2 i) (Q2.hfix130_10_2 i) _)
      colCert_130_10_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T130_12
      hfix130_12 hinj130_12 hcardT130_12
      (fun i => conj_mem_of_fixedPoints _ _ (T130_12 i) (hfix130_12 i) _)
      ⟨130, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T130_12_2 Q2.hfix130_12_2 Q2.hinj130_12_2
      Q2.hcardT130_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_12_2 i) (Q2.hfix130_12_2 i) _)
      colCert_130_12_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T130_12
      hfix130_12 hinj130_12 hcardT130_12
      (fun i => conj_mem_of_fixedPoints _ _ (T130_12 i) (hfix130_12 i) _)
      ⟨130, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T130_12_2 Q2.hfix130_12_2 Q2.hinj130_12_2
      Q2.hcardT130_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_12_2 i) (Q2.hfix130_12_2 i) _)
      colCert_130_12_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T130_12
      hfix130_12 hinj130_12 hcardT130_12
      (fun i => conj_mem_of_fixedPoints _ _ (T130_12 i) (hfix130_12 i) _)
      ⟨130, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T130_12_2 Q2.hfix130_12_2 Q2.hinj130_12_2
      Q2.hcardT130_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_12_2 i) (Q2.hfix130_12_2 i) _)
      colCert_130_12_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T130_12
      hfix130_12 hinj130_12 hcardT130_12
      (fun i => conj_mem_of_fixedPoints _ _ (T130_12 i) (hfix130_12 i) _)
      ⟨130, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T130_12_2 Q2.hfix130_12_2 Q2.hinj130_12_2
      Q2.hcardT130_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_12_2 i) (Q2.hfix130_12_2 i) _)
      colCert_130_12_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T130_12
      hfix130_12 hinj130_12 hcardT130_12
      (fun i => conj_mem_of_fixedPoints _ _ (T130_12 i) (hfix130_12 i) _)
      ⟨130, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T130_12_2 Q2.hfix130_12_2 Q2.hinj130_12_2
      Q2.hcardT130_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_12_2 i) (Q2.hfix130_12_2 i) _)
      colCert_130_12_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T130_21
      hfix130_21 hinj130_21 hcardT130_21
      (fun i => conj_mem_of_fixedPoints _ _ (T130_21 i) (hfix130_21 i) _)
      ⟨130, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T130_21_2 Q2.hfix130_21_2 Q2.hinj130_21_2
      Q2.hcardT130_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_21_2 i) (Q2.hfix130_21_2 i) _)
      colCert_130_21_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T130_21
      hfix130_21 hinj130_21 hcardT130_21
      (fun i => conj_mem_of_fixedPoints _ _ (T130_21 i) (hfix130_21 i) _)
      ⟨130, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T130_21_2 Q2.hfix130_21_2 Q2.hinj130_21_2
      Q2.hcardT130_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_21_2 i) (Q2.hfix130_21_2 i) _)
      colCert_130_21_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T130_21
      hfix130_21 hinj130_21 hcardT130_21
      (fun i => conj_mem_of_fixedPoints _ _ (T130_21 i) (hfix130_21 i) _)
      ⟨130, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T130_21_2 Q2.hfix130_21_2 Q2.hinj130_21_2
      Q2.hcardT130_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_21_2 i) (Q2.hfix130_21_2 i) _)
      colCert_130_21_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T130_21
      hfix130_21 hinj130_21 hcardT130_21
      (fun i => conj_mem_of_fixedPoints _ _ (T130_21 i) (hfix130_21 i) _)
      ⟨130, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T130_21_2 Q2.hfix130_21_2 Q2.hinj130_21_2
      Q2.hcardT130_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_21_2 i) (Q2.hfix130_21_2 i) _)
      colCert_130_21_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T130_21
      hfix130_21 hinj130_21 hcardT130_21
      (fun i => conj_mem_of_fixedPoints _ _ (T130_21 i) (hfix130_21 i) _)
      ⟨130, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T130_21_2 Q2.hfix130_21_2 Q2.hinj130_21_2
      Q2.hcardT130_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_21_2 i) (Q2.hfix130_21_2 i) _)
      colCert_130_21_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T130_21
      hfix130_21 hinj130_21 hcardT130_21
      (fun i => conj_mem_of_fixedPoints _ _ (T130_21 i) (hfix130_21 i) _)
      ⟨130, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T130_21_2 Q2.hfix130_21_2 Q2.hinj130_21_2
      Q2.hcardT130_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_21_2 i) (Q2.hfix130_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T130_21 = colFn colCertDiv_130_21_5.D1 (m := 5) from colCertDiv_130_21_5.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 5 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T130_21_2 = colFn colCertDiv_130_21_5.D2 (m := 5) from colCertDiv_130_21_5.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_21_5_match


theorem leaf_130_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T130_21
      hfix130_21 hinj130_21 hcardT130_21
      (fun i => conj_mem_of_fixedPoints _ _ (T130_21 i) (hfix130_21 i) _)
      ⟨130, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T130_21_2 Q2.hfix130_21_2 Q2.hinj130_21_2
      Q2.hcardT130_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_21_2 i) (Q2.hfix130_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T130_21 = colFn colCertDiv_130_21_10.D1 (m := 5) from colCertDiv_130_21_10.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 10 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T130_21_2 = colFn colCertDiv_130_21_10.D2 (m := 5) from colCertDiv_130_21_10.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_21_10_match


theorem leaf_130_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T130_21
      hfix130_21 hinj130_21 hcardT130_21
      (fun i => conj_mem_of_fixedPoints _ _ (T130_21 i) (hfix130_21 i) _)
      ⟨130, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T130_21_2 Q2.hfix130_21_2 Q2.hinj130_21_2
      Q2.hcardT130_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_21_2 i) (Q2.hfix130_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T130_21 = colFn colCertDiv_130_21_15.D1 (m := 5) from colCertDiv_130_21_15.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 15 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T130_21_2 = colFn colCertDiv_130_21_15.D2 (m := 5) from colCertDiv_130_21_15.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_21_15_match


theorem leaf_130_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T130_21
      hfix130_21 hinj130_21 hcardT130_21
      (fun i => conj_mem_of_fixedPoints _ _ (T130_21 i) (hfix130_21 i) _)
      ⟨130, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T130_21_2 Q2.hfix130_21_2 Q2.hinj130_21_2
      Q2.hcardT130_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_21_2 i) (Q2.hfix130_21_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp) : ↥(reps ⟨21, by decide⟩)) : Coordinate 1)
        T130_21 = colFn colCertDiv_130_21_20.D1 (m := 5) from colCertDiv_130_21_20.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨21, by decide⟩ 20 hp : ↥(Q2.reps ⟨21, by decide⟩)) : Coordinate 2)
        Q2.T130_21_2 = colFn colCertDiv_130_21_20.D2 (m := 5) from colCertDiv_130_21_20.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_21_20_match


theorem leaf_130_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T130_30
      hfix130_30 hinj130_30 hcardT130_30
      (fun i => conj_mem_of_fixedPoints _ _ (T130_30 i) (hfix130_30 i) _)
      ⟨130, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T130_30_2 Q2.hfix130_30_2 Q2.hinj130_30_2
      Q2.hcardT130_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_30_2 i) (Q2.hfix130_30_2 i) _)
      colCert_130_30_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T130_30
      hfix130_30 hinj130_30 hcardT130_30
      (fun i => conj_mem_of_fixedPoints _ _ (T130_30 i) (hfix130_30 i) _)
      ⟨130, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T130_30_2 Q2.hfix130_30_2 Q2.hinj130_30_2
      Q2.hcardT130_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_30_2 i) (Q2.hfix130_30_2 i) _)
      colCert_130_30_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T130_30
      hfix130_30 hinj130_30 hcardT130_30
      (fun i => conj_mem_of_fixedPoints _ _ (T130_30 i) (hfix130_30 i) _)
      ⟨130, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T130_30_2 Q2.hfix130_30_2 Q2.hinj130_30_2
      Q2.hcardT130_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_30_2 i) (Q2.hfix130_30_2 i) _)
      colCert_130_30_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T130_30
      hfix130_30 hinj130_30 hcardT130_30
      (fun i => conj_mem_of_fixedPoints _ _ (T130_30 i) (hfix130_30 i) _)
      ⟨130, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T130_30_2 Q2.hfix130_30_2 Q2.hinj130_30_2
      Q2.hcardT130_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_30_2 i) (Q2.hfix130_30_2 i) _)
      colCert_130_30_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T130_30
      hfix130_30 hinj130_30 hcardT130_30
      (fun i => conj_mem_of_fixedPoints _ _ (T130_30 i) (hfix130_30 i) _)
      ⟨130, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T130_30_2 Q2.hfix130_30_2 Q2.hinj130_30_2
      Q2.hcardT130_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_30_2 i) (Q2.hfix130_30_2 i) _)
      colCert_130_30_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T130_30
      hfix130_30 hinj130_30 hcardT130_30
      (fun i => conj_mem_of_fixedPoints _ _ (T130_30 i) (hfix130_30 i) _)
      ⟨130, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T130_30_2 Q2.hfix130_30_2 Q2.hinj130_30_2
      Q2.hcardT130_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_30_2 i) (Q2.hfix130_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T130_30 = colFn colCertDiv_130_30_5.D1 (m := 5) from colCertDiv_130_30_5.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T130_30_2 = colFn colCertDiv_130_30_5.D2 (m := 5) from colCertDiv_130_30_5.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_30_5_match


theorem leaf_130_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T130_30
      hfix130_30 hinj130_30 hcardT130_30
      (fun i => conj_mem_of_fixedPoints _ _ (T130_30 i) (hfix130_30 i) _)
      ⟨130, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T130_30_2 Q2.hfix130_30_2 Q2.hinj130_30_2
      Q2.hcardT130_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_30_2 i) (Q2.hfix130_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T130_30 = colFn colCertDiv_130_30_10.D1 (m := 5) from colCertDiv_130_30_10.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T130_30_2 = colFn colCertDiv_130_30_10.D2 (m := 5) from colCertDiv_130_30_10.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_30_10_match


theorem leaf_130_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T130_30
      hfix130_30 hinj130_30 hcardT130_30
      (fun i => conj_mem_of_fixedPoints _ _ (T130_30 i) (hfix130_30 i) _)
      ⟨130, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T130_30_2 Q2.hfix130_30_2 Q2.hinj130_30_2
      Q2.hcardT130_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_30_2 i) (Q2.hfix130_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T130_30 = colFn colCertDiv_130_30_15.D1 (m := 5) from colCertDiv_130_30_15.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 15 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T130_30_2 = colFn colCertDiv_130_30_15.D2 (m := 5) from colCertDiv_130_30_15.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_30_15_match


theorem leaf_130_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T130_30
      hfix130_30 hinj130_30 hcardT130_30
      (fun i => conj_mem_of_fixedPoints _ _ (T130_30 i) (hfix130_30 i) _)
      ⟨130, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T130_30_2 Q2.hfix130_30_2 Q2.hinj130_30_2
      Q2.hcardT130_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_30_2 i) (Q2.hfix130_30_2 i) _)
      colCert_130_30_20.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T130_36
      hfix130_36 hinj130_36 hcardT130_36
      (fun i => conj_mem_of_fixedPoints _ _ (T130_36 i) (hfix130_36 i) _)
      ⟨130, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T130_36_2 Q2.hfix130_36_2 Q2.hinj130_36_2
      Q2.hcardT130_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_36_2 i) (Q2.hfix130_36_2 i) _)
      colCert_130_36_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T130_36
      hfix130_36 hinj130_36 hcardT130_36
      (fun i => conj_mem_of_fixedPoints _ _ (T130_36 i) (hfix130_36 i) _)
      ⟨130, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T130_36_2 Q2.hfix130_36_2 Q2.hinj130_36_2
      Q2.hcardT130_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_36_2 i) (Q2.hfix130_36_2 i) _)
      colCert_130_36_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T130_36
      hfix130_36 hinj130_36 hcardT130_36
      (fun i => conj_mem_of_fixedPoints _ _ (T130_36 i) (hfix130_36 i) _)
      ⟨130, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T130_36_2 Q2.hfix130_36_2 Q2.hinj130_36_2
      Q2.hcardT130_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_36_2 i) (Q2.hfix130_36_2 i) _)
      colCert_130_36_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T130_36
      hfix130_36 hinj130_36 hcardT130_36
      (fun i => conj_mem_of_fixedPoints _ _ (T130_36 i) (hfix130_36 i) _)
      ⟨130, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T130_36_2 Q2.hfix130_36_2 Q2.hinj130_36_2
      Q2.hcardT130_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_36_2 i) (Q2.hfix130_36_2 i) _)
      colCert_130_36_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T130_36
      hfix130_36 hinj130_36 hcardT130_36
      (fun i => conj_mem_of_fixedPoints _ _ (T130_36 i) (hfix130_36 i) _)
      ⟨130, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T130_36_2 Q2.hfix130_36_2 Q2.hinj130_36_2
      Q2.hcardT130_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_36_2 i) (Q2.hfix130_36_2 i) _)
      colCert_130_36_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T130_36
      hfix130_36 hinj130_36 hcardT130_36
      (fun i => conj_mem_of_fixedPoints _ _ (T130_36 i) (hfix130_36 i) _)
      ⟨130, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T130_36_2 Q2.hfix130_36_2 Q2.hinj130_36_2
      Q2.hcardT130_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_36_2 i) (Q2.hfix130_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T130_36 = colFn colCertDiv_130_36_5.D1 (m := 5) from colCertDiv_130_36_5.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T130_36_2 = colFn colCertDiv_130_36_5.D2 (m := 5) from colCertDiv_130_36_5.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_36_5_match


theorem leaf_130_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T130_36
      hfix130_36 hinj130_36 hcardT130_36
      (fun i => conj_mem_of_fixedPoints _ _ (T130_36 i) (hfix130_36 i) _)
      ⟨130, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T130_36_2 Q2.hfix130_36_2 Q2.hinj130_36_2
      Q2.hcardT130_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_36_2 i) (Q2.hfix130_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T130_36 = colFn colCertDiv_130_36_10.D1 (m := 5) from colCertDiv_130_36_10.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T130_36_2 = colFn colCertDiv_130_36_10.D2 (m := 5) from colCertDiv_130_36_10.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_36_10_match


theorem leaf_130_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T130_36
      hfix130_36 hinj130_36 hcardT130_36
      (fun i => conj_mem_of_fixedPoints _ _ (T130_36 i) (hfix130_36 i) _)
      ⟨130, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T130_36_2 Q2.hfix130_36_2 Q2.hinj130_36_2
      Q2.hcardT130_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_36_2 i) (Q2.hfix130_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T130_36 = colFn colCertDiv_130_36_15.D1 (m := 5) from colCertDiv_130_36_15.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 15 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T130_36_2 = colFn colCertDiv_130_36_15.D2 (m := 5) from colCertDiv_130_36_15.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_36_15_match


theorem leaf_130_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T130_36
      hfix130_36 hinj130_36 hcardT130_36
      (fun i => conj_mem_of_fixedPoints _ _ (T130_36 i) (hfix130_36 i) _)
      ⟨130, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T130_36_2 Q2.hfix130_36_2 Q2.hinj130_36_2
      Q2.hcardT130_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_36_2 i) (Q2.hfix130_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T130_36 = colFn colCertDiv_130_36_20.D1 (m := 5) from colCertDiv_130_36_20.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T130_36_2 = colFn colCertDiv_130_36_20.D2 (m := 5) from colCertDiv_130_36_20.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_36_20_match


theorem leaf_130_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T130_38
      hfix130_38 hinj130_38 hcardT130_38
      (fun i => conj_mem_of_fixedPoints _ _ (T130_38 i) (hfix130_38 i) _)
      ⟨130, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T130_38_2 Q2.hfix130_38_2 Q2.hinj130_38_2
      Q2.hcardT130_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_38_2 i) (Q2.hfix130_38_2 i) _)
      colCert_130_38_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T130_38
      hfix130_38 hinj130_38 hcardT130_38
      (fun i => conj_mem_of_fixedPoints _ _ (T130_38 i) (hfix130_38 i) _)
      ⟨130, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T130_38_2 Q2.hfix130_38_2 Q2.hinj130_38_2
      Q2.hcardT130_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_38_2 i) (Q2.hfix130_38_2 i) _)
      colCert_130_38_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T130_38
      hfix130_38 hinj130_38 hcardT130_38
      (fun i => conj_mem_of_fixedPoints _ _ (T130_38 i) (hfix130_38 i) _)
      ⟨130, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T130_38_2 Q2.hfix130_38_2 Q2.hinj130_38_2
      Q2.hcardT130_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_38_2 i) (Q2.hfix130_38_2 i) _)
      colCert_130_38_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T130_38
      hfix130_38 hinj130_38 hcardT130_38
      (fun i => conj_mem_of_fixedPoints _ _ (T130_38 i) (hfix130_38 i) _)
      ⟨130, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T130_38_2 Q2.hfix130_38_2 Q2.hinj130_38_2
      Q2.hcardT130_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_38_2 i) (Q2.hfix130_38_2 i) _)
      colCert_130_38_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T130_38
      hfix130_38 hinj130_38 hcardT130_38
      (fun i => conj_mem_of_fixedPoints _ _ (T130_38 i) (hfix130_38 i) _)
      ⟨130, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T130_38_2 Q2.hfix130_38_2 Q2.hinj130_38_2
      Q2.hcardT130_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_38_2 i) (Q2.hfix130_38_2 i) _)
      colCert_130_38_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T130_38
      hfix130_38 hinj130_38 hcardT130_38
      (fun i => conj_mem_of_fixedPoints _ _ (T130_38 i) (hfix130_38 i) _)
      ⟨130, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T130_38_2 Q2.hfix130_38_2 Q2.hinj130_38_2
      Q2.hcardT130_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_38_2 i) (Q2.hfix130_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T130_38 = colFn colCertDiv_130_38_5.D1 (m := 5) from colCertDiv_130_38_5.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T130_38_2 = colFn colCertDiv_130_38_5.D2 (m := 5) from colCertDiv_130_38_5.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_38_5_match


theorem leaf_130_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T130_38
      hfix130_38 hinj130_38 hcardT130_38
      (fun i => conj_mem_of_fixedPoints _ _ (T130_38 i) (hfix130_38 i) _)
      ⟨130, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T130_38_2 Q2.hfix130_38_2 Q2.hinj130_38_2
      Q2.hcardT130_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_38_2 i) (Q2.hfix130_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T130_38 = colFn colCertDiv_130_38_10.D1 (m := 5) from colCertDiv_130_38_10.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T130_38_2 = colFn colCertDiv_130_38_10.D2 (m := 5) from colCertDiv_130_38_10.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_38_10_match


theorem leaf_130_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T130_38
      hfix130_38 hinj130_38 hcardT130_38
      (fun i => conj_mem_of_fixedPoints _ _ (T130_38 i) (hfix130_38 i) _)
      ⟨130, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T130_38_2 Q2.hfix130_38_2 Q2.hinj130_38_2
      Q2.hcardT130_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_38_2 i) (Q2.hfix130_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T130_38 = colFn colCertDiv_130_38_15.D1 (m := 5) from colCertDiv_130_38_15.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T130_38_2 = colFn colCertDiv_130_38_15.D2 (m := 5) from colCertDiv_130_38_15.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_38_15_match


theorem leaf_130_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T130_38
      hfix130_38 hinj130_38 hcardT130_38
      (fun i => conj_mem_of_fixedPoints _ _ (T130_38 i) (hfix130_38 i) _)
      ⟨130, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T130_38_2 Q2.hfix130_38_2 Q2.hinj130_38_2
      Q2.hcardT130_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_38_2 i) (Q2.hfix130_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T130_38 = colFn colCertDiv_130_38_20.D1 (m := 5) from colCertDiv_130_38_20.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T130_38_2 = colFn colCertDiv_130_38_20.D2 (m := 5) from colCertDiv_130_38_20.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_38_20_match


theorem leaf_130_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T130_44
      hfix130_44 hinj130_44 hcardT130_44
      (fun i => conj_mem_of_fixedPoints _ _ (T130_44 i) (hfix130_44 i) _)
      ⟨130, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T130_44_2 Q2.hfix130_44_2 Q2.hinj130_44_2
      Q2.hcardT130_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_44_2 i) (Q2.hfix130_44_2 i) _)
      colCert_130_44_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T130_44
      hfix130_44 hinj130_44 hcardT130_44
      (fun i => conj_mem_of_fixedPoints _ _ (T130_44 i) (hfix130_44 i) _)
      ⟨130, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T130_44_2 Q2.hfix130_44_2 Q2.hinj130_44_2
      Q2.hcardT130_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_44_2 i) (Q2.hfix130_44_2 i) _)
      colCert_130_44_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T130_44
      hfix130_44 hinj130_44 hcardT130_44
      (fun i => conj_mem_of_fixedPoints _ _ (T130_44 i) (hfix130_44 i) _)
      ⟨130, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T130_44_2 Q2.hfix130_44_2 Q2.hinj130_44_2
      Q2.hcardT130_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_44_2 i) (Q2.hfix130_44_2 i) _)
      colCert_130_44_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T130_44
      hfix130_44 hinj130_44 hcardT130_44
      (fun i => conj_mem_of_fixedPoints _ _ (T130_44 i) (hfix130_44 i) _)
      ⟨130, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T130_44_2 Q2.hfix130_44_2 Q2.hinj130_44_2
      Q2.hcardT130_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_44_2 i) (Q2.hfix130_44_2 i) _)
      colCert_130_44_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T130_44
      hfix130_44 hinj130_44 hcardT130_44
      (fun i => conj_mem_of_fixedPoints _ _ (T130_44 i) (hfix130_44 i) _)
      ⟨130, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T130_44_2 Q2.hfix130_44_2 Q2.hinj130_44_2
      Q2.hcardT130_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_44_2 i) (Q2.hfix130_44_2 i) _)
      colCert_130_44_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T130_44
      hfix130_44 hinj130_44 hcardT130_44
      (fun i => conj_mem_of_fixedPoints _ _ (T130_44 i) (hfix130_44 i) _)
      ⟨130, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T130_44_2 Q2.hfix130_44_2 Q2.hinj130_44_2
      Q2.hcardT130_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_44_2 i) (Q2.hfix130_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T130_44 = colFn colCertDiv_130_44_5.D1 (m := 5) from colCertDiv_130_44_5.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 5 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T130_44_2 = colFn colCertDiv_130_44_5.D2 (m := 5) from colCertDiv_130_44_5.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_44_5_match


theorem leaf_130_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T130_44
      hfix130_44 hinj130_44 hcardT130_44
      (fun i => conj_mem_of_fixedPoints _ _ (T130_44 i) (hfix130_44 i) _)
      ⟨130, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T130_44_2 Q2.hfix130_44_2 Q2.hinj130_44_2
      Q2.hcardT130_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_44_2 i) (Q2.hfix130_44_2 i) _)
      colCert_130_44_10.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T130_44
      hfix130_44 hinj130_44 hcardT130_44
      (fun i => conj_mem_of_fixedPoints _ _ (T130_44 i) (hfix130_44 i) _)
      ⟨130, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T130_44_2 Q2.hfix130_44_2 Q2.hinj130_44_2
      Q2.hcardT130_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_44_2 i) (Q2.hfix130_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T130_44 = colFn colCertDiv_130_44_15.D1 (m := 5) from colCertDiv_130_44_15.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 15 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T130_44_2 = colFn colCertDiv_130_44_15.D2 (m := 5) from colCertDiv_130_44_15.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_44_15_match


theorem leaf_130_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T130_44
      hfix130_44 hinj130_44 hcardT130_44
      (fun i => conj_mem_of_fixedPoints _ _ (T130_44 i) (hfix130_44 i) _)
      ⟨130, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T130_44_2 Q2.hfix130_44_2 Q2.hinj130_44_2
      Q2.hcardT130_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_44_2 i) (Q2.hfix130_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T130_44 = colFn colCertDiv_130_44_20.D1 (m := 5) from colCertDiv_130_44_20.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 20 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T130_44_2 = colFn colCertDiv_130_44_20.D2 (m := 5) from colCertDiv_130_44_20.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_44_20_match


theorem leaf_130_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T130_52
      hfix130_52 hinj130_52 hcardT130_52
      (fun i => conj_mem_of_fixedPoints _ _ (T130_52 i) (hfix130_52 i) _)
      ⟨130, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T130_52_2 Q2.hfix130_52_2 Q2.hinj130_52_2
      Q2.hcardT130_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_52_2 i) (Q2.hfix130_52_2 i) _)
      colCert_130_52_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T130_52
      hfix130_52 hinj130_52 hcardT130_52
      (fun i => conj_mem_of_fixedPoints _ _ (T130_52 i) (hfix130_52 i) _)
      ⟨130, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T130_52_2 Q2.hfix130_52_2 Q2.hinj130_52_2
      Q2.hcardT130_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_52_2 i) (Q2.hfix130_52_2 i) _)
      colCert_130_52_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T130_52
      hfix130_52 hinj130_52 hcardT130_52
      (fun i => conj_mem_of_fixedPoints _ _ (T130_52 i) (hfix130_52 i) _)
      ⟨130, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T130_52_2 Q2.hfix130_52_2 Q2.hinj130_52_2
      Q2.hcardT130_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_52_2 i) (Q2.hfix130_52_2 i) _)
      colCert_130_52_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T130_52
      hfix130_52 hinj130_52 hcardT130_52
      (fun i => conj_mem_of_fixedPoints _ _ (T130_52 i) (hfix130_52 i) _)
      ⟨130, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T130_52_2 Q2.hfix130_52_2 Q2.hinj130_52_2
      Q2.hcardT130_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_52_2 i) (Q2.hfix130_52_2 i) _)
      colCert_130_52_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T130_52
      hfix130_52 hinj130_52 hcardT130_52
      (fun i => conj_mem_of_fixedPoints _ _ (T130_52 i) (hfix130_52 i) _)
      ⟨130, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T130_52_2 Q2.hfix130_52_2 Q2.hinj130_52_2
      Q2.hcardT130_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_52_2 i) (Q2.hfix130_52_2 i) _)
      colCert_130_52_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T130_52
      hfix130_52 hinj130_52 hcardT130_52
      (fun i => conj_mem_of_fixedPoints _ _ (T130_52 i) (hfix130_52 i) _)
      ⟨130, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T130_52_2 Q2.hfix130_52_2 Q2.hinj130_52_2
      Q2.hcardT130_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_52_2 i) (Q2.hfix130_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T130_52 = colFn colCertDiv_130_52_5.D1 (m := 5) from colCertDiv_130_52_5.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T130_52_2 = colFn colCertDiv_130_52_5.D2 (m := 5) from colCertDiv_130_52_5.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_52_5_match


theorem leaf_130_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T130_52
      hfix130_52 hinj130_52 hcardT130_52
      (fun i => conj_mem_of_fixedPoints _ _ (T130_52 i) (hfix130_52 i) _)
      ⟨130, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T130_52_2 Q2.hfix130_52_2 Q2.hinj130_52_2
      Q2.hcardT130_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_52_2 i) (Q2.hfix130_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T130_52 = colFn colCertDiv_130_52_10.D1 (m := 5) from colCertDiv_130_52_10.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T130_52_2 = colFn colCertDiv_130_52_10.D2 (m := 5) from colCertDiv_130_52_10.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_52_10_match


theorem leaf_130_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T130_52
      hfix130_52 hinj130_52 hcardT130_52
      (fun i => conj_mem_of_fixedPoints _ _ (T130_52 i) (hfix130_52 i) _)
      ⟨130, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T130_52_2 Q2.hfix130_52_2 Q2.hinj130_52_2
      Q2.hcardT130_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_52_2 i) (Q2.hfix130_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T130_52 = colFn colCertDiv_130_52_15.D1 (m := 5) from colCertDiv_130_52_15.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T130_52_2 = colFn colCertDiv_130_52_15.D2 (m := 5) from colCertDiv_130_52_15.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_52_15_match


theorem leaf_130_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T130_52
      hfix130_52 hinj130_52 hcardT130_52
      (fun i => conj_mem_of_fixedPoints _ _ (T130_52 i) (hfix130_52 i) _)
      ⟨130, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T130_52_2 Q2.hfix130_52_2 Q2.hinj130_52_2
      Q2.hcardT130_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_52_2 i) (Q2.hfix130_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T130_52 = colFn colCertDiv_130_52_20.D1 (m := 5) from colCertDiv_130_52_20.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T130_52_2 = colFn colCertDiv_130_52_20.D2 (m := 5) from colCertDiv_130_52_20.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_52_20_match


theorem leaf_130_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T130_53
      hfix130_53 hinj130_53 hcardT130_53
      (fun i => conj_mem_of_fixedPoints _ _ (T130_53 i) (hfix130_53 i) _)
      ⟨130, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T130_53_2 Q2.hfix130_53_2 Q2.hinj130_53_2
      Q2.hcardT130_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_53_2 i) (Q2.hfix130_53_2 i) _)
      colCert_130_53_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T130_53
      hfix130_53 hinj130_53 hcardT130_53
      (fun i => conj_mem_of_fixedPoints _ _ (T130_53 i) (hfix130_53 i) _)
      ⟨130, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T130_53_2 Q2.hfix130_53_2 Q2.hinj130_53_2
      Q2.hcardT130_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_53_2 i) (Q2.hfix130_53_2 i) _)
      colCert_130_53_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T130_53
      hfix130_53 hinj130_53 hcardT130_53
      (fun i => conj_mem_of_fixedPoints _ _ (T130_53 i) (hfix130_53 i) _)
      ⟨130, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T130_53_2 Q2.hfix130_53_2 Q2.hinj130_53_2
      Q2.hcardT130_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_53_2 i) (Q2.hfix130_53_2 i) _)
      colCert_130_53_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T130_53
      hfix130_53 hinj130_53 hcardT130_53
      (fun i => conj_mem_of_fixedPoints _ _ (T130_53 i) (hfix130_53 i) _)
      ⟨130, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T130_53_2 Q2.hfix130_53_2 Q2.hinj130_53_2
      Q2.hcardT130_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_53_2 i) (Q2.hfix130_53_2 i) _)
      colCert_130_53_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T130_53
      hfix130_53 hinj130_53 hcardT130_53
      (fun i => conj_mem_of_fixedPoints _ _ (T130_53 i) (hfix130_53 i) _)
      ⟨130, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T130_53_2 Q2.hfix130_53_2 Q2.hinj130_53_2
      Q2.hcardT130_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_53_2 i) (Q2.hfix130_53_2 i) _)
      colCert_130_53_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T130_53
      hfix130_53 hinj130_53 hcardT130_53
      (fun i => conj_mem_of_fixedPoints _ _ (T130_53 i) (hfix130_53 i) _)
      ⟨130, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T130_53_2 Q2.hfix130_53_2 Q2.hinj130_53_2
      Q2.hcardT130_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_53_2 i) (Q2.hfix130_53_2 i) _)
      colCert_130_53_5.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T130_53
      hfix130_53 hinj130_53 hcardT130_53
      (fun i => conj_mem_of_fixedPoints _ _ (T130_53 i) (hfix130_53 i) _)
      ⟨130, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T130_53_2 Q2.hfix130_53_2 Q2.hinj130_53_2
      Q2.hcardT130_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_53_2 i) (Q2.hfix130_53_2 i) _)
      colCert_130_53_10.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T130_53
      hfix130_53 hinj130_53 hcardT130_53
      (fun i => conj_mem_of_fixedPoints _ _ (T130_53 i) (hfix130_53 i) _)
      ⟨130, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T130_53_2 Q2.hfix130_53_2 Q2.hinj130_53_2
      Q2.hcardT130_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_53_2 i) (Q2.hfix130_53_2 i) _)
      colCert_130_53_15.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T130_53
      hfix130_53 hinj130_53 hcardT130_53
      (fun i => conj_mem_of_fixedPoints _ _ (T130_53 i) (hfix130_53 i) _)
      ⟨130, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T130_53_2 Q2.hfix130_53_2 Q2.hinj130_53_2
      Q2.hcardT130_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_53_2 i) (Q2.hfix130_53_2 i) _)
      colCert_130_53_20.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_82_0 (hp : 0 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp)) T130_82
      hfix130_82 hinj130_82 hcardT130_82
      (fun i => conj_mem_of_fixedPoints _ _ (T130_82 i) (hfix130_82 i) _)
      ⟨130, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 0 hp) Q2.T130_82_2 Q2.hfix130_82_2 Q2.hinj130_82_2
      Q2.hcardT130_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_82_2 i) (Q2.hfix130_82_2 i) _)
      colCert_130_82_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_82_1 (hp : 1 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp)) T130_82
      hfix130_82 hinj130_82 hcardT130_82
      (fun i => conj_mem_of_fixedPoints _ _ (T130_82 i) (hfix130_82 i) _)
      ⟨130, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 1 hp) Q2.T130_82_2 Q2.hfix130_82_2 Q2.hinj130_82_2
      Q2.hcardT130_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_82_2 i) (Q2.hfix130_82_2 i) _)
      colCert_130_82_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_82_2 (hp : 2 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp)) T130_82
      hfix130_82 hinj130_82 hcardT130_82
      (fun i => conj_mem_of_fixedPoints _ _ (T130_82 i) (hfix130_82 i) _)
      ⟨130, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 2 hp) Q2.T130_82_2 Q2.hfix130_82_2 Q2.hinj130_82_2
      Q2.hcardT130_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_82_2 i) (Q2.hfix130_82_2 i) _)
      colCert_130_82_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_82_3 (hp : 3 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp)) T130_82
      hfix130_82 hinj130_82 hcardT130_82
      (fun i => conj_mem_of_fixedPoints _ _ (T130_82 i) (hfix130_82 i) _)
      ⟨130, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 3 hp) Q2.T130_82_2 Q2.hfix130_82_2 Q2.hinj130_82_2
      Q2.hcardT130_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_82_2 i) (Q2.hfix130_82_2 i) _)
      colCert_130_82_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_82_4 (hp : 4 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp)) T130_82
      hfix130_82 hinj130_82 hcardT130_82
      (fun i => conj_mem_of_fixedPoints _ _ (T130_82 i) (hfix130_82 i) _)
      ⟨130, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 4 hp) Q2.T130_82_2 Q2.hfix130_82_2 Q2.hinj130_82_2
      Q2.hcardT130_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_82_2 i) (Q2.hfix130_82_2 i) _)
      colCert_130_82_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_82_5 (hp : 5 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp)) T130_82
      hfix130_82 hinj130_82 hcardT130_82
      (fun i => conj_mem_of_fixedPoints _ _ (T130_82 i) (hfix130_82 i) _)
      ⟨130, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 5 hp) Q2.T130_82_2 Q2.hfix130_82_2 Q2.hinj130_82_2
      Q2.hcardT130_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_82_2 i) (Q2.hfix130_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T130_82 = colFn colCertDiv_130_82_5.D1 (m := 5) from colCertDiv_130_82_5.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 5 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T130_82_2 = colFn colCertDiv_130_82_5.D2 (m := 5) from colCertDiv_130_82_5.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_82_5_match


theorem leaf_130_82_10 (hp : 10 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp)) T130_82
      hfix130_82 hinj130_82 hcardT130_82
      (fun i => conj_mem_of_fixedPoints _ _ (T130_82 i) (hfix130_82 i) _)
      ⟨130, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 10 hp) Q2.T130_82_2 Q2.hfix130_82_2 Q2.hinj130_82_2
      Q2.hcardT130_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_82_2 i) (Q2.hfix130_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T130_82 = colFn colCertDiv_130_82_10.D1 (m := 5) from colCertDiv_130_82_10.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 10 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T130_82_2 = colFn colCertDiv_130_82_10.D2 (m := 5) from colCertDiv_130_82_10.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_82_10_match


theorem leaf_130_82_15 (hp : 15 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp)) T130_82
      hfix130_82 hinj130_82 hcardT130_82
      (fun i => conj_mem_of_fixedPoints _ _ (T130_82 i) (hfix130_82 i) _)
      ⟨130, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 15 hp) Q2.T130_82_2 Q2.hfix130_82_2 Q2.hinj130_82_2
      Q2.hcardT130_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_82_2 i) (Q2.hfix130_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T130_82 = colFn colCertDiv_130_82_15.D1 (m := 5) from colCertDiv_130_82_15.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 15 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T130_82_2 = colFn colCertDiv_130_82_15.D2 (m := 5) from colCertDiv_130_82_15.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_82_15_match


theorem leaf_130_82_20 (hp : 20 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp)) T130_82
      hfix130_82 hinj130_82 hcardT130_82
      (fun i => conj_mem_of_fixedPoints _ _ (T130_82 i) (hfix130_82 i) _)
      ⟨130, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 20 hp) Q2.T130_82_2 Q2.hfix130_82_2 Q2.hinj130_82_2
      Q2.hcardT130_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_82_2 i) (Q2.hfix130_82_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp) : ↥(reps ⟨82, by decide⟩)) : Coordinate 1)
        T130_82 = colFn colCertDiv_130_82_20.D1 (m := 5) from colCertDiv_130_82_20.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨82, by decide⟩ 20 hp : ↥(Q2.reps ⟨82, by decide⟩)) : Coordinate 2)
        Q2.T130_82_2 = colFn colCertDiv_130_82_20.D2 (m := 5) from colCertDiv_130_82_20.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_82_20_match


theorem leaf_130_92_0 (hp : 0 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 0 (transLenTr ⟨92, by decide⟩ 0 hp)) T130_92
      hfix130_92 hinj130_92 hcardT130_92
      (fun i => conj_mem_of_fixedPoints _ _ (T130_92 i) (hfix130_92 i) _)
      ⟨130, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 0 hp) Q2.T130_92_2 Q2.hfix130_92_2 Q2.hinj130_92_2
      Q2.hcardT130_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_92_2 i) (Q2.hfix130_92_2 i) _)
      colCert_130_92_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_92_1 (hp : 1 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 1 (transLenTr ⟨92, by decide⟩ 1 hp)) T130_92
      hfix130_92 hinj130_92 hcardT130_92
      (fun i => conj_mem_of_fixedPoints _ _ (T130_92 i) (hfix130_92 i) _)
      ⟨130, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 1 hp) Q2.T130_92_2 Q2.hfix130_92_2 Q2.hinj130_92_2
      Q2.hcardT130_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_92_2 i) (Q2.hfix130_92_2 i) _)
      colCert_130_92_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_92_2 (hp : 2 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 2 (transLenTr ⟨92, by decide⟩ 2 hp)) T130_92
      hfix130_92 hinj130_92 hcardT130_92
      (fun i => conj_mem_of_fixedPoints _ _ (T130_92 i) (hfix130_92 i) _)
      ⟨130, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 2 hp) Q2.T130_92_2 Q2.hfix130_92_2 Q2.hinj130_92_2
      Q2.hcardT130_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_92_2 i) (Q2.hfix130_92_2 i) _)
      colCert_130_92_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_92_3 (hp : 3 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 3 (transLenTr ⟨92, by decide⟩ 3 hp)) T130_92
      hfix130_92 hinj130_92 hcardT130_92
      (fun i => conj_mem_of_fixedPoints _ _ (T130_92 i) (hfix130_92 i) _)
      ⟨130, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 3 hp) Q2.T130_92_2 Q2.hfix130_92_2 Q2.hinj130_92_2
      Q2.hcardT130_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_92_2 i) (Q2.hfix130_92_2 i) _)
      colCert_130_92_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_92_4 (hp : 4 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 4 (transLenTr ⟨92, by decide⟩ 4 hp)) T130_92
      hfix130_92 hinj130_92 hcardT130_92
      (fun i => conj_mem_of_fixedPoints _ _ (T130_92 i) (hfix130_92 i) _)
      ⟨130, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 4 hp) Q2.T130_92_2 Q2.hfix130_92_2 Q2.hinj130_92_2
      Q2.hcardT130_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_92_2 i) (Q2.hfix130_92_2 i) _)
      colCert_130_92_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_92_5 (hp : 5 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp)) T130_92
      hfix130_92 hinj130_92 hcardT130_92
      (fun i => conj_mem_of_fixedPoints _ _ (T130_92 i) (hfix130_92 i) _)
      ⟨130, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 5 hp) Q2.T130_92_2 Q2.hfix130_92_2 Q2.hinj130_92_2
      Q2.hcardT130_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_92_2 i) (Q2.hfix130_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 5 (transLenTr ⟨92, by decide⟩ 5 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T130_92 = colFn colCertDiv_130_92_5.D1 (m := 5) from colCertDiv_130_92_5.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 5 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T130_92_2 = colFn colCertDiv_130_92_5.D2 (m := 5) from colCertDiv_130_92_5.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_92_5_match


theorem leaf_130_92_10 (hp : 10 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp)) T130_92
      hfix130_92 hinj130_92 hcardT130_92
      (fun i => conj_mem_of_fixedPoints _ _ (T130_92 i) (hfix130_92 i) _)
      ⟨130, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 10 hp) Q2.T130_92_2 Q2.hfix130_92_2 Q2.hinj130_92_2
      Q2.hcardT130_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_92_2 i) (Q2.hfix130_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 10 (transLenTr ⟨92, by decide⟩ 10 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T130_92 = colFn colCertDiv_130_92_10.D1 (m := 5) from colCertDiv_130_92_10.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 10 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T130_92_2 = colFn colCertDiv_130_92_10.D2 (m := 5) from colCertDiv_130_92_10.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_92_10_match


theorem leaf_130_92_15 (hp : 15 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp)) T130_92
      hfix130_92 hinj130_92 hcardT130_92
      (fun i => conj_mem_of_fixedPoints _ _ (T130_92 i) (hfix130_92 i) _)
      ⟨130, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 15 hp) Q2.T130_92_2 Q2.hfix130_92_2 Q2.hinj130_92_2
      Q2.hcardT130_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_92_2 i) (Q2.hfix130_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 15 (transLenTr ⟨92, by decide⟩ 15 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T130_92 = colFn colCertDiv_130_92_15.D1 (m := 5) from colCertDiv_130_92_15.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 15 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T130_92_2 = colFn colCertDiv_130_92_15.D2 (m := 5) from colCertDiv_130_92_15.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_92_15_match


theorem leaf_130_92_20 (hp : 20 < (Q2.transData.getD 92 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨92, by decide⟩ : Fin 148)) (colE2 ⟨92, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨92, by decide⟩ : Fin 148))
        (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨92, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp)) T130_92
      hfix130_92 hinj130_92 hcardT130_92
      (fun i => conj_mem_of_fixedPoints _ _ (T130_92 i) (hfix130_92 i) _)
      ⟨130, by decide⟩ ⟨92, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨92, by decide⟩ 20 hp) Q2.T130_92_2 Q2.hfix130_92_2 Q2.hinj130_92_2
      Q2.hcardT130_92_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_92_2 i) (Q2.hfix130_92_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨92, by decide⟩ 20 (transLenTr ⟨92, by decide⟩ 20 hp) : ↥(reps ⟨92, by decide⟩)) : Coordinate 1)
        T130_92 = colFn colCertDiv_130_92_20.D1 (m := 5) from colCertDiv_130_92_20.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨92, by decide⟩ 20 hp : ↥(Q2.reps ⟨92, by decide⟩)) : Coordinate 2)
        Q2.T130_92_2 = colFn colCertDiv_130_92_20.D2 (m := 5) from colCertDiv_130_92_20.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_92_20_match


theorem leaf_130_98_0 (hp : 0 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 0 (transLenTr ⟨98, by decide⟩ 0 hp)) T130_98
      hfix130_98 hinj130_98 hcardT130_98
      (fun i => conj_mem_of_fixedPoints _ _ (T130_98 i) (hfix130_98 i) _)
      ⟨130, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 0 hp) Q2.T130_98_2 Q2.hfix130_98_2 Q2.hinj130_98_2
      Q2.hcardT130_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_98_2 i) (Q2.hfix130_98_2 i) _)
      colCert_130_98_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_98_1 (hp : 1 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 1 (transLenTr ⟨98, by decide⟩ 1 hp)) T130_98
      hfix130_98 hinj130_98 hcardT130_98
      (fun i => conj_mem_of_fixedPoints _ _ (T130_98 i) (hfix130_98 i) _)
      ⟨130, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 1 hp) Q2.T130_98_2 Q2.hfix130_98_2 Q2.hinj130_98_2
      Q2.hcardT130_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_98_2 i) (Q2.hfix130_98_2 i) _)
      colCert_130_98_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_98_2 (hp : 2 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 2 (transLenTr ⟨98, by decide⟩ 2 hp)) T130_98
      hfix130_98 hinj130_98 hcardT130_98
      (fun i => conj_mem_of_fixedPoints _ _ (T130_98 i) (hfix130_98 i) _)
      ⟨130, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 2 hp) Q2.T130_98_2 Q2.hfix130_98_2 Q2.hinj130_98_2
      Q2.hcardT130_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_98_2 i) (Q2.hfix130_98_2 i) _)
      colCert_130_98_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_98_3 (hp : 3 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 3 (transLenTr ⟨98, by decide⟩ 3 hp)) T130_98
      hfix130_98 hinj130_98 hcardT130_98
      (fun i => conj_mem_of_fixedPoints _ _ (T130_98 i) (hfix130_98 i) _)
      ⟨130, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 3 hp) Q2.T130_98_2 Q2.hfix130_98_2 Q2.hinj130_98_2
      Q2.hcardT130_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_98_2 i) (Q2.hfix130_98_2 i) _)
      colCert_130_98_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_98_4 (hp : 4 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 4 (transLenTr ⟨98, by decide⟩ 4 hp)) T130_98
      hfix130_98 hinj130_98 hcardT130_98
      (fun i => conj_mem_of_fixedPoints _ _ (T130_98 i) (hfix130_98 i) _)
      ⟨130, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 4 hp) Q2.T130_98_2 Q2.hfix130_98_2 Q2.hinj130_98_2
      Q2.hcardT130_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_98_2 i) (Q2.hfix130_98_2 i) _)
      colCert_130_98_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_98_5 (hp : 5 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp)) T130_98
      hfix130_98 hinj130_98 hcardT130_98
      (fun i => conj_mem_of_fixedPoints _ _ (T130_98 i) (hfix130_98 i) _)
      ⟨130, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 5 hp) Q2.T130_98_2 Q2.hfix130_98_2 Q2.hinj130_98_2
      Q2.hcardT130_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_98_2 i) (Q2.hfix130_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 5 (transLenTr ⟨98, by decide⟩ 5 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T130_98 = colFn colCertDiv_130_98_5.D1 (m := 5) from colCertDiv_130_98_5.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 5 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T130_98_2 = colFn colCertDiv_130_98_5.D2 (m := 5) from colCertDiv_130_98_5.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_98_5_match


theorem leaf_130_98_10 (hp : 10 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp)) T130_98
      hfix130_98 hinj130_98 hcardT130_98
      (fun i => conj_mem_of_fixedPoints _ _ (T130_98 i) (hfix130_98 i) _)
      ⟨130, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 10 hp) Q2.T130_98_2 Q2.hfix130_98_2 Q2.hinj130_98_2
      Q2.hcardT130_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_98_2 i) (Q2.hfix130_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 10 (transLenTr ⟨98, by decide⟩ 10 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T130_98 = colFn colCertDiv_130_98_10.D1 (m := 5) from colCertDiv_130_98_10.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 10 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T130_98_2 = colFn colCertDiv_130_98_10.D2 (m := 5) from colCertDiv_130_98_10.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_98_10_match


theorem leaf_130_98_15 (hp : 15 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 15 (transLenTr ⟨98, by decide⟩ 15 hp)) T130_98
      hfix130_98 hinj130_98 hcardT130_98
      (fun i => conj_mem_of_fixedPoints _ _ (T130_98 i) (hfix130_98 i) _)
      ⟨130, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 15 hp) Q2.T130_98_2 Q2.hfix130_98_2 Q2.hinj130_98_2
      Q2.hcardT130_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_98_2 i) (Q2.hfix130_98_2 i) _)
      colCert_130_98_15.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_98_20 (hp : 20 < (Q2.transData.getD 98 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨98, by decide⟩ : Fin 148)) (colE2 ⟨98, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨98, by decide⟩ : Fin 148))
        (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨98, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp)) T130_98
      hfix130_98 hinj130_98 hcardT130_98
      (fun i => conj_mem_of_fixedPoints _ _ (T130_98 i) (hfix130_98 i) _)
      ⟨130, by decide⟩ ⟨98, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨98, by decide⟩ 20 hp) Q2.T130_98_2 Q2.hfix130_98_2 Q2.hinj130_98_2
      Q2.hcardT130_98_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_98_2 i) (Q2.hfix130_98_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨98, by decide⟩ 20 (transLenTr ⟨98, by decide⟩ 20 hp) : ↥(reps ⟨98, by decide⟩)) : Coordinate 1)
        T130_98 = colFn colCertDiv_130_98_20.D1 (m := 5) from colCertDiv_130_98_20.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨98, by decide⟩ 20 hp : ↥(Q2.reps ⟨98, by decide⟩)) : Coordinate 2)
        Q2.T130_98_2 = colFn colCertDiv_130_98_20.D2 (m := 5) from colCertDiv_130_98_20.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_98_20_match


theorem leaf_130_100_0 (hp : 0 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 0 (transLenTr ⟨100, by decide⟩ 0 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 0 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      colCert_130_100_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_100_1 (hp : 1 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 1 (transLenTr ⟨100, by decide⟩ 1 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 1 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      colCert_130_100_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_100_2 (hp : 2 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 2 (transLenTr ⟨100, by decide⟩ 2 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 2 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      colCert_130_100_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_100_3 (hp : 3 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 3 (transLenTr ⟨100, by decide⟩ 3 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 3 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      colCert_130_100_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_100_4 (hp : 4 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 4 (transLenTr ⟨100, by decide⟩ 4 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 4 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      colCert_130_100_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_100_5 (hp : 5 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 5 (transLenTr ⟨100, by decide⟩ 5 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 5 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      colCert_130_100_5.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_100_10 (hp : 10 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 10 (transLenTr ⟨100, by decide⟩ 10 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 10 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      colCert_130_100_10.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_100_15 (hp : 15 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 15 (transLenTr ⟨100, by decide⟩ 15 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 15 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      colCert_130_100_15.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_100_20 (hp : 20 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 20 (transLenTr ⟨100, by decide⟩ 20 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 20 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      colCert_130_100_20.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_100_25 (hp : 25 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 25 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 25 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 25 (transLenTr ⟨100, by decide⟩ 25 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T130_100 = colFn colCertDiv_130_100_25.D1 (m := 5) from colCertDiv_130_100_25.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 25 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T130_100_2 = colFn colCertDiv_130_100_25.D2 (m := 5) from colCertDiv_130_100_25.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_100_25_match


theorem leaf_130_100_50 (hp : 50 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 50 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 50 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 50 (transLenTr ⟨100, by decide⟩ 50 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T130_100 = colFn colCertDiv_130_100_50.D1 (m := 5) from colCertDiv_130_100_50.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 50 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T130_100_2 = colFn colCertDiv_130_100_50.D2 (m := 5) from colCertDiv_130_100_50.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_100_50_match


theorem leaf_130_100_75 (hp : 75 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 75 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 75 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 75 (transLenTr ⟨100, by decide⟩ 75 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T130_100 = colFn colCertDiv_130_100_75.D1 (m := 5) from colCertDiv_130_100_75.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 75 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T130_100_2 = colFn colCertDiv_130_100_75.D2 (m := 5) from colCertDiv_130_100_75.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_100_75_match


theorem leaf_130_100_100 (hp : 100 < (Q2.transData.getD 100 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨100, by decide⟩ : Fin 148)) (colE2 ⟨100, by decide⟩ 100 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨100, by decide⟩ : Fin 148))
        (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨100, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp)) T130_100
      hfix130_100 hinj130_100 hcardT130_100
      (fun i => conj_mem_of_fixedPoints _ _ (T130_100 i) (hfix130_100 i) _)
      ⟨130, by decide⟩ ⟨100, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨100, by decide⟩ 100 hp) Q2.T130_100_2 Q2.hfix130_100_2 Q2.hinj130_100_2
      Q2.hcardT130_100_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_100_2 i) (Q2.hfix130_100_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨100, by decide⟩ 100 (transLenTr ⟨100, by decide⟩ 100 hp) : ↥(reps ⟨100, by decide⟩)) : Coordinate 1)
        T130_100 = colFn colCertDiv_130_100_100.D1 (m := 5) from colCertDiv_130_100_100.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨100, by decide⟩ 100 hp : ↥(Q2.reps ⟨100, by decide⟩)) : Coordinate 2)
        Q2.T130_100_2 = colFn colCertDiv_130_100_100.D2 (m := 5) from colCertDiv_130_100_100.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_100_100_match


theorem leaf_130_106_0 (hp : 0 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp)) T130_106
      hfix130_106 hinj130_106 hcardT130_106
      (fun i => conj_mem_of_fixedPoints _ _ (T130_106 i) (hfix130_106 i) _)
      ⟨130, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 0 hp) Q2.T130_106_2 Q2.hfix130_106_2 Q2.hinj130_106_2
      Q2.hcardT130_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_106_2 i) (Q2.hfix130_106_2 i) _)
      colCert_130_106_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_106_1 (hp : 1 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp)) T130_106
      hfix130_106 hinj130_106 hcardT130_106
      (fun i => conj_mem_of_fixedPoints _ _ (T130_106 i) (hfix130_106 i) _)
      ⟨130, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 1 hp) Q2.T130_106_2 Q2.hfix130_106_2 Q2.hinj130_106_2
      Q2.hcardT130_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_106_2 i) (Q2.hfix130_106_2 i) _)
      colCert_130_106_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_106_2 (hp : 2 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp)) T130_106
      hfix130_106 hinj130_106 hcardT130_106
      (fun i => conj_mem_of_fixedPoints _ _ (T130_106 i) (hfix130_106 i) _)
      ⟨130, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 2 hp) Q2.T130_106_2 Q2.hfix130_106_2 Q2.hinj130_106_2
      Q2.hcardT130_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_106_2 i) (Q2.hfix130_106_2 i) _)
      colCert_130_106_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_106_3 (hp : 3 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp)) T130_106
      hfix130_106 hinj130_106 hcardT130_106
      (fun i => conj_mem_of_fixedPoints _ _ (T130_106 i) (hfix130_106 i) _)
      ⟨130, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 3 hp) Q2.T130_106_2 Q2.hfix130_106_2 Q2.hinj130_106_2
      Q2.hcardT130_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_106_2 i) (Q2.hfix130_106_2 i) _)
      colCert_130_106_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_106_4 (hp : 4 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp)) T130_106
      hfix130_106 hinj130_106 hcardT130_106
      (fun i => conj_mem_of_fixedPoints _ _ (T130_106 i) (hfix130_106 i) _)
      ⟨130, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 4 hp) Q2.T130_106_2 Q2.hfix130_106_2 Q2.hinj130_106_2
      Q2.hcardT130_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_106_2 i) (Q2.hfix130_106_2 i) _)
      colCert_130_106_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_106_5 (hp : 5 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp)) T130_106
      hfix130_106 hinj130_106 hcardT130_106
      (fun i => conj_mem_of_fixedPoints _ _ (T130_106 i) (hfix130_106 i) _)
      ⟨130, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 5 hp) Q2.T130_106_2 Q2.hfix130_106_2 Q2.hinj130_106_2
      Q2.hcardT130_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_106_2 i) (Q2.hfix130_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T130_106 = colFn colCertDiv_130_106_5.D1 (m := 5) from colCertDiv_130_106_5.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 5 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T130_106_2 = colFn colCertDiv_130_106_5.D2 (m := 5) from colCertDiv_130_106_5.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_106_5_match


theorem leaf_130_106_10 (hp : 10 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp)) T130_106
      hfix130_106 hinj130_106 hcardT130_106
      (fun i => conj_mem_of_fixedPoints _ _ (T130_106 i) (hfix130_106 i) _)
      ⟨130, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 10 hp) Q2.T130_106_2 Q2.hfix130_106_2 Q2.hinj130_106_2
      Q2.hcardT130_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_106_2 i) (Q2.hfix130_106_2 i) _)
      colCert_130_106_10.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_106_15 (hp : 15 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp)) T130_106
      hfix130_106 hinj130_106 hcardT130_106
      (fun i => conj_mem_of_fixedPoints _ _ (T130_106 i) (hfix130_106 i) _)
      ⟨130, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 15 hp) Q2.T130_106_2 Q2.hfix130_106_2 Q2.hinj130_106_2
      Q2.hcardT130_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_106_2 i) (Q2.hfix130_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T130_106 = colFn colCertDiv_130_106_15.D1 (m := 5) from colCertDiv_130_106_15.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 15 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T130_106_2 = colFn colCertDiv_130_106_15.D2 (m := 5) from colCertDiv_130_106_15.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_106_15_match


theorem leaf_130_106_20 (hp : 20 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨130, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp)) T130_106
      hfix130_106 hinj130_106 hcardT130_106
      (fun i => conj_mem_of_fixedPoints _ _ (T130_106 i) (hfix130_106 i) _)
      ⟨130, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 20 hp) Q2.T130_106_2 Q2.hfix130_106_2 Q2.hinj130_106_2
      Q2.hcardT130_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_106_2 i) (Q2.hfix130_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨130, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T130_106 = colFn colCertDiv_130_106_20.D1 (m := 5) from colCertDiv_130_106_20.bind1,
    show colData2 (⟨130, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 20 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T130_106_2 = colFn colCertDiv_130_106_20.D2 (m := 5) from colCertDiv_130_106_20.bind2]
  rw [alnId_130 j hj]
  exact fastcode_of_div ⟨130, by decide⟩ _ _ _
    ((alnId_130 j hj) ▸ Q2.listedAt (⟨130, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨130, by decide⟩ : Fin 148) hj hq).1) colCertDiv_130_106_20_match


theorem leaf_130_114_0 (hp : 0 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 0 (transLenTr ⟨114, by decide⟩ 0 hp)) T130_114
      hfix130_114 hinj130_114 hcardT130_114
      (fun i => conj_mem_of_fixedPoints _ _ (T130_114 i) (hfix130_114 i) _)
      ⟨130, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 0 hp) Q2.T130_114_2 Q2.hfix130_114_2 Q2.hinj130_114_2
      Q2.hcardT130_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_114_2 i) (Q2.hfix130_114_2 i) _)
      colCert_130_114_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_114_1 (hp : 1 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 1 (transLenTr ⟨114, by decide⟩ 1 hp)) T130_114
      hfix130_114 hinj130_114 hcardT130_114
      (fun i => conj_mem_of_fixedPoints _ _ (T130_114 i) (hfix130_114 i) _)
      ⟨130, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 1 hp) Q2.T130_114_2 Q2.hfix130_114_2 Q2.hinj130_114_2
      Q2.hcardT130_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_114_2 i) (Q2.hfix130_114_2 i) _)
      colCert_130_114_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_114_2 (hp : 2 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 2 (transLenTr ⟨114, by decide⟩ 2 hp)) T130_114
      hfix130_114 hinj130_114 hcardT130_114
      (fun i => conj_mem_of_fixedPoints _ _ (T130_114 i) (hfix130_114 i) _)
      ⟨130, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 2 hp) Q2.T130_114_2 Q2.hfix130_114_2 Q2.hinj130_114_2
      Q2.hcardT130_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_114_2 i) (Q2.hfix130_114_2 i) _)
      colCert_130_114_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_114_3 (hp : 3 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 3 (transLenTr ⟨114, by decide⟩ 3 hp)) T130_114
      hfix130_114 hinj130_114 hcardT130_114
      (fun i => conj_mem_of_fixedPoints _ _ (T130_114 i) (hfix130_114 i) _)
      ⟨130, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 3 hp) Q2.T130_114_2 Q2.hfix130_114_2 Q2.hinj130_114_2
      Q2.hcardT130_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_114_2 i) (Q2.hfix130_114_2 i) _)
      colCert_130_114_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_114_4 (hp : 4 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 4 (transLenTr ⟨114, by decide⟩ 4 hp)) T130_114
      hfix130_114 hinj130_114 hcardT130_114
      (fun i => conj_mem_of_fixedPoints _ _ (T130_114 i) (hfix130_114 i) _)
      ⟨130, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 4 hp) Q2.T130_114_2 Q2.hfix130_114_2 Q2.hinj130_114_2
      Q2.hcardT130_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_114_2 i) (Q2.hfix130_114_2 i) _)
      colCert_130_114_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_114_5 (hp : 5 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 5 (transLenTr ⟨114, by decide⟩ 5 hp)) T130_114
      hfix130_114 hinj130_114 hcardT130_114
      (fun i => conj_mem_of_fixedPoints _ _ (T130_114 i) (hfix130_114 i) _)
      ⟨130, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 5 hp) Q2.T130_114_2 Q2.hfix130_114_2 Q2.hinj130_114_2
      Q2.hcardT130_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_114_2 i) (Q2.hfix130_114_2 i) _)
      colCert_130_114_5.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_114_10 (hp : 10 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 10 (transLenTr ⟨114, by decide⟩ 10 hp)) T130_114
      hfix130_114 hinj130_114 hcardT130_114
      (fun i => conj_mem_of_fixedPoints _ _ (T130_114 i) (hfix130_114 i) _)
      ⟨130, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 10 hp) Q2.T130_114_2 Q2.hfix130_114_2 Q2.hinj130_114_2
      Q2.hcardT130_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_114_2 i) (Q2.hfix130_114_2 i) _)
      colCert_130_114_10.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_114_15 (hp : 15 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 15 (transLenTr ⟨114, by decide⟩ 15 hp)) T130_114
      hfix130_114 hinj130_114 hcardT130_114
      (fun i => conj_mem_of_fixedPoints _ _ (T130_114 i) (hfix130_114 i) _)
      ⟨130, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 15 hp) Q2.T130_114_2 Q2.hfix130_114_2 Q2.hinj130_114_2
      Q2.hcardT130_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_114_2 i) (Q2.hfix130_114_2 i) _)
      colCert_130_114_15.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_114_20 (hp : 20 < (Q2.transData.getD 114 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨114, by decide⟩ : Fin 148)) (colE2 ⟨114, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨114, by decide⟩ : Fin 148))
        (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨114, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨114, by decide⟩ 20 (transLenTr ⟨114, by decide⟩ 20 hp)) T130_114
      hfix130_114 hinj130_114 hcardT130_114
      (fun i => conj_mem_of_fixedPoints _ _ (T130_114 i) (hfix130_114 i) _)
      ⟨130, by decide⟩ ⟨114, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨114, by decide⟩ 20 hp) Q2.T130_114_2 Q2.hfix130_114_2 Q2.hinj130_114_2
      Q2.hcardT130_114_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_114_2 i) (Q2.hfix130_114_2 i) _)
      colCert_130_114_20.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_0 (hp : 0 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 0 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 0 (transLenTr ⟨130, by decide⟩ 0 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 0 (transLenTr ⟨130, by decide⟩ 0 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 0 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_0.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_1 (hp : 1 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 1 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 1 (transLenTr ⟨130, by decide⟩ 1 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 1 (transLenTr ⟨130, by decide⟩ 1 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 1 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_1.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_2 (hp : 2 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 2 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 2 (transLenTr ⟨130, by decide⟩ 2 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 2 (transLenTr ⟨130, by decide⟩ 2 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 2 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_2.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_3 (hp : 3 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 3 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 3 (transLenTr ⟨130, by decide⟩ 3 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 3 (transLenTr ⟨130, by decide⟩ 3 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 3 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_3.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_4 (hp : 4 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 4 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 4 (transLenTr ⟨130, by decide⟩ 4 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 4 (transLenTr ⟨130, by decide⟩ 4 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 4 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_4.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_5 (hp : 5 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 5 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 5 (transLenTr ⟨130, by decide⟩ 5 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 5 (transLenTr ⟨130, by decide⟩ 5 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 5 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_5.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_6 (hp : 6 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 6 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 6 (transLenTr ⟨130, by decide⟩ 6 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 6 (transLenTr ⟨130, by decide⟩ 6 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 6 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_6.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_7 (hp : 7 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 7 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 7 (transLenTr ⟨130, by decide⟩ 7 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 7 (transLenTr ⟨130, by decide⟩ 7 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 7 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_7.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_8 (hp : 8 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 8 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 8 (transLenTr ⟨130, by decide⟩ 8 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 8 (transLenTr ⟨130, by decide⟩ 8 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 8 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_8.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_9 (hp : 9 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 9 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 9 (transLenTr ⟨130, by decide⟩ 9 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 9 (transLenTr ⟨130, by decide⟩ 9 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 9 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_9.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_10 (hp : 10 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 10 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 10 (transLenTr ⟨130, by decide⟩ 10 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 10 (transLenTr ⟨130, by decide⟩ 10 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 10 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_10.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_11 (hp : 11 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 11 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 11 (transLenTr ⟨130, by decide⟩ 11 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 11 (transLenTr ⟨130, by decide⟩ 11 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 11 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_11.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_12 (hp : 12 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 12 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 12 (transLenTr ⟨130, by decide⟩ 12 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 12 (transLenTr ⟨130, by decide⟩ 12 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 12 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_12.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_13 (hp : 13 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 13 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 13 (transLenTr ⟨130, by decide⟩ 13 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 13 (transLenTr ⟨130, by decide⟩ 13 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 13 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_13.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_14 (hp : 14 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 14 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 14 (transLenTr ⟨130, by decide⟩ 14 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 14 (transLenTr ⟨130, by decide⟩ 14 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 14 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_14.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_15 (hp : 15 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 15 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 15 (transLenTr ⟨130, by decide⟩ 15 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 15 (transLenTr ⟨130, by decide⟩ 15 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 15 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_15.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_16 (hp : 16 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 16 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 16 (transLenTr ⟨130, by decide⟩ 16 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 16 (transLenTr ⟨130, by decide⟩ 16 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 16 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_16.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_17 (hp : 17 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 17 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 17 (transLenTr ⟨130, by decide⟩ 17 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 17 (transLenTr ⟨130, by decide⟩ 17 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 17 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_17.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_18 (hp : 18 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 18 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 18 (transLenTr ⟨130, by decide⟩ 18 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 18 (transLenTr ⟨130, by decide⟩ 18 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 18 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_18.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_19 (hp : 19 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 19 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 19 (transLenTr ⟨130, by decide⟩ 19 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 19 (transLenTr ⟨130, by decide⟩ 19 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 19 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_19.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_20 (hp : 20 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 20 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 20 (transLenTr ⟨130, by decide⟩ 20 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 20 (transLenTr ⟨130, by decide⟩ 20 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 20 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_20.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_21 (hp : 21 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 21 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 21 (transLenTr ⟨130, by decide⟩ 21 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 21 (transLenTr ⟨130, by decide⟩ 21 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 21 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_21.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_22 (hp : 22 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 22 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 22 (transLenTr ⟨130, by decide⟩ 22 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 22 (transLenTr ⟨130, by decide⟩ 22 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 22 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_22.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_23 (hp : 23 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 23 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 23 (transLenTr ⟨130, by decide⟩ 23 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 23 (transLenTr ⟨130, by decide⟩ 23 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 23 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_23.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_130_130_24 (hp : 24 < (Q2.transData.getD 130 []).length)
    (j : Nat) (hj : j < (repChars.getD 130 []).length)
    (hq : (normIsRep.getD 130 []).getD j false = true) :
    species (Q2.reps (⟨130, by decide⟩ : Fin 148)) (colE2 ⟨130, by decide⟩ 24 hp)
        (rowE2 (⟨130, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨130, by decide⟩ : Fin 148))
        (colE1 ⟨130, by decide⟩ 24 (transLenTr ⟨130, by decide⟩ 24 hp))
        (rowE1 (⟨130, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨130, by decide⟩ : Fin 148) ⟨130, by decide⟩ _
      (validAt ⟨130, by decide⟩ (listedAt ⟨130, by decide⟩ hj))
      (colE1 ⟨130, by decide⟩ 24 (transLenTr ⟨130, by decide⟩ 24 hp)) T130_130
      hfix130_130 hinj130_130 hcardT130_130
      (fun i => conj_mem_of_fixedPoints _ _ (T130_130 i) (hfix130_130 i) _)
      ⟨130, by decide⟩ ⟨130, by decide⟩ _
      (Q2.validAt ⟨130, by decide⟩ (Q2.listedAt ⟨130, by decide⟩
        (alnCheck_rep ⟨130, by decide⟩ hj hq).1))
      (colE2 ⟨130, by decide⟩ 24 hp) Q2.T130_130_2 Q2.hfix130_130_2 Q2.hinj130_130_2
      Q2.hcardT130_130_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T130_130_2 i) (Q2.hfix130_130_2 i) _)
      colCert_130_130_24.hD ?_).symm
  rw [alnId_130 j hj]


theorem leaf_131_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T131_4
      hfix131_4 hinj131_4 hcardT131_4
      (fun i => conj_mem_of_fixedPoints _ _ (T131_4 i) (hfix131_4 i) _)
      ⟨131, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T131_4_2 Q2.hfix131_4_2 Q2.hinj131_4_2
      Q2.hcardT131_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_4_2 i) (Q2.hfix131_4_2 i) _)
      colCert_131_4_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T131_4
      hfix131_4 hinj131_4 hcardT131_4
      (fun i => conj_mem_of_fixedPoints _ _ (T131_4 i) (hfix131_4 i) _)
      ⟨131, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T131_4_2 Q2.hfix131_4_2 Q2.hinj131_4_2
      Q2.hcardT131_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_4_2 i) (Q2.hfix131_4_2 i) _)
      colCert_131_4_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T131_4
      hfix131_4 hinj131_4 hcardT131_4
      (fun i => conj_mem_of_fixedPoints _ _ (T131_4 i) (hfix131_4 i) _)
      ⟨131, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T131_4_2 Q2.hfix131_4_2 Q2.hinj131_4_2
      Q2.hcardT131_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_4_2 i) (Q2.hfix131_4_2 i) _)
      colCert_131_4_2.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T131_4
      hfix131_4 hinj131_4 hcardT131_4
      (fun i => conj_mem_of_fixedPoints _ _ (T131_4 i) (hfix131_4 i) _)
      ⟨131, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T131_4_2 Q2.hfix131_4_2 Q2.hinj131_4_2
      Q2.hcardT131_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_4_2 i) (Q2.hfix131_4_2 i) _)
      colCert_131_4_3.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T131_4
      hfix131_4 hinj131_4 hcardT131_4
      (fun i => conj_mem_of_fixedPoints _ _ (T131_4 i) (hfix131_4 i) _)
      ⟨131, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T131_4_2 Q2.hfix131_4_2 Q2.hinj131_4_2
      Q2.hcardT131_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_4_2 i) (Q2.hfix131_4_2 i) _)
      colCert_131_4_4.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T131_10
      hfix131_10 hinj131_10 hcardT131_10
      (fun i => conj_mem_of_fixedPoints _ _ (T131_10 i) (hfix131_10 i) _)
      ⟨131, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T131_10_2 Q2.hfix131_10_2 Q2.hinj131_10_2
      Q2.hcardT131_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_10_2 i) (Q2.hfix131_10_2 i) _)
      colCert_131_10_0.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T131_10
      hfix131_10 hinj131_10 hcardT131_10
      (fun i => conj_mem_of_fixedPoints _ _ (T131_10 i) (hfix131_10 i) _)
      ⟨131, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T131_10_2 Q2.hfix131_10_2 Q2.hinj131_10_2
      Q2.hcardT131_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_10_2 i) (Q2.hfix131_10_2 i) _)
      colCert_131_10_1.hD ?_).symm
  rw [alnId_131 j hj]


theorem leaf_131_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 131 []).length)
    (hq : (normIsRep.getD 131 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨131, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨131, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨131, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨131, by decide⟩ (listedAt ⟨131, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T131_10
      hfix131_10 hinj131_10 hcardT131_10
      (fun i => conj_mem_of_fixedPoints _ _ (T131_10 i) (hfix131_10 i) _)
      ⟨131, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨131, by decide⟩ (Q2.listedAt ⟨131, by decide⟩
        (alnCheck_rep ⟨131, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T131_10_2 Q2.hfix131_10_2 Q2.hinj131_10_2
      Q2.hcardT131_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T131_10_2 i) (Q2.hfix131_10_2 i) _)
      colCert_131_10_2.hD ?_).symm
  rw [alnId_131 j hj]


end LeanDring.P5Presentation
