/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C016
import LeanDring.P5.Data.ColCdd.C017
import LeanDring.P5.Data.ColRestCheap.C074
import LeanDring.P5.Data.ColRestCheap.C075
import LeanDring.P5.Data.ColRestCheap.C076
import LeanDring.P5.Data.ColRestCheap.C077
import LeanDring.P5.Data.EntryK.C036
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C020
import LeanDring.P5.Data.SpeciesDiv.C021
import LeanDring.P5.Data.SpeciesDiv.C022
import LeanDring.P5.Data.SpeciesDiv.C023

/-! # Stage-5 leaves, chunk 38 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_134_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T134_28
      hfix134_28 hinj134_28 hcardT134_28
      (fun i => conj_mem_of_fixedPoints _ _ (T134_28 i) (hfix134_28 i) _)
      ⟨134, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T134_28_2 Q2.hfix134_28_2 Q2.hinj134_28_2
      Q2.hcardT134_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_28_2 i) (Q2.hfix134_28_2 i) _)
      colCert_134_28_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T134_28
      hfix134_28 hinj134_28 hcardT134_28
      (fun i => conj_mem_of_fixedPoints _ _ (T134_28 i) (hfix134_28 i) _)
      ⟨134, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T134_28_2 Q2.hfix134_28_2 Q2.hinj134_28_2
      Q2.hcardT134_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_28_2 i) (Q2.hfix134_28_2 i) _)
      colCert_134_28_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T134_28
      hfix134_28 hinj134_28 hcardT134_28
      (fun i => conj_mem_of_fixedPoints _ _ (T134_28 i) (hfix134_28 i) _)
      ⟨134, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T134_28_2 Q2.hfix134_28_2 Q2.hinj134_28_2
      Q2.hcardT134_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_28_2 i) (Q2.hfix134_28_2 i) _)
      colCert_134_28_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T134_28
      hfix134_28 hinj134_28 hcardT134_28
      (fun i => conj_mem_of_fixedPoints _ _ (T134_28 i) (hfix134_28 i) _)
      ⟨134, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T134_28_2 Q2.hfix134_28_2 Q2.hinj134_28_2
      Q2.hcardT134_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_28_2 i) (Q2.hfix134_28_2 i) _)
      colCert_134_28_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T134_28
      hfix134_28 hinj134_28 hcardT134_28
      (fun i => conj_mem_of_fixedPoints _ _ (T134_28 i) (hfix134_28 i) _)
      ⟨134, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T134_28_2 Q2.hfix134_28_2 Q2.hinj134_28_2
      Q2.hcardT134_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_28_2 i) (Q2.hfix134_28_2 i) _)
      colCert_134_28_5.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T134_28
      hfix134_28 hinj134_28 hcardT134_28
      (fun i => conj_mem_of_fixedPoints _ _ (T134_28 i) (hfix134_28 i) _)
      ⟨134, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T134_28_2 Q2.hfix134_28_2 Q2.hinj134_28_2
      Q2.hcardT134_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_28_2 i) (Q2.hfix134_28_2 i) _)
      colCert_134_28_10.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T134_28
      hfix134_28 hinj134_28 hcardT134_28
      (fun i => conj_mem_of_fixedPoints _ _ (T134_28 i) (hfix134_28 i) _)
      ⟨134, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T134_28_2 Q2.hfix134_28_2 Q2.hinj134_28_2
      Q2.hcardT134_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_28_2 i) (Q2.hfix134_28_2 i) _)
      colCert_134_28_15.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T134_28
      hfix134_28 hinj134_28 hcardT134_28
      (fun i => conj_mem_of_fixedPoints _ _ (T134_28 i) (hfix134_28 i) _)
      ⟨134, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T134_28_2 Q2.hfix134_28_2 Q2.hinj134_28_2
      Q2.hcardT134_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_28_2 i) (Q2.hfix134_28_2 i) _)
      colCert_134_28_20.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_37_0 (hp : 0 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 0 (transLenTr ⟨37, by decide⟩ 0 hp)) T134_37
      hfix134_37 hinj134_37 hcardT134_37
      (fun i => conj_mem_of_fixedPoints _ _ (T134_37 i) (hfix134_37 i) _)
      ⟨134, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 0 hp) Q2.T134_37_2 Q2.hfix134_37_2 Q2.hinj134_37_2
      Q2.hcardT134_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_37_2 i) (Q2.hfix134_37_2 i) _)
      colCert_134_37_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_37_1 (hp : 1 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 1 (transLenTr ⟨37, by decide⟩ 1 hp)) T134_37
      hfix134_37 hinj134_37 hcardT134_37
      (fun i => conj_mem_of_fixedPoints _ _ (T134_37 i) (hfix134_37 i) _)
      ⟨134, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 1 hp) Q2.T134_37_2 Q2.hfix134_37_2 Q2.hinj134_37_2
      Q2.hcardT134_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_37_2 i) (Q2.hfix134_37_2 i) _)
      colCert_134_37_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_37_2 (hp : 2 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 2 (transLenTr ⟨37, by decide⟩ 2 hp)) T134_37
      hfix134_37 hinj134_37 hcardT134_37
      (fun i => conj_mem_of_fixedPoints _ _ (T134_37 i) (hfix134_37 i) _)
      ⟨134, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 2 hp) Q2.T134_37_2 Q2.hfix134_37_2 Q2.hinj134_37_2
      Q2.hcardT134_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_37_2 i) (Q2.hfix134_37_2 i) _)
      colCert_134_37_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_37_3 (hp : 3 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 3 (transLenTr ⟨37, by decide⟩ 3 hp)) T134_37
      hfix134_37 hinj134_37 hcardT134_37
      (fun i => conj_mem_of_fixedPoints _ _ (T134_37 i) (hfix134_37 i) _)
      ⟨134, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 3 hp) Q2.T134_37_2 Q2.hfix134_37_2 Q2.hinj134_37_2
      Q2.hcardT134_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_37_2 i) (Q2.hfix134_37_2 i) _)
      colCert_134_37_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_37_4 (hp : 4 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 4 (transLenTr ⟨37, by decide⟩ 4 hp)) T134_37
      hfix134_37 hinj134_37 hcardT134_37
      (fun i => conj_mem_of_fixedPoints _ _ (T134_37 i) (hfix134_37 i) _)
      ⟨134, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 4 hp) Q2.T134_37_2 Q2.hfix134_37_2 Q2.hinj134_37_2
      Q2.hcardT134_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_37_2 i) (Q2.hfix134_37_2 i) _)
      colCert_134_37_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_37_5 (hp : 5 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp)) T134_37
      hfix134_37 hinj134_37 hcardT134_37
      (fun i => conj_mem_of_fixedPoints _ _ (T134_37 i) (hfix134_37 i) _)
      ⟨134, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 5 hp) Q2.T134_37_2 Q2.hfix134_37_2 Q2.hinj134_37_2
      Q2.hcardT134_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_37_2 i) (Q2.hfix134_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 5 (transLenTr ⟨37, by decide⟩ 5 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T134_37 = colFn colCertDiv_134_37_5.D1 (m := 5) from colCertDiv_134_37_5.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 5 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T134_37_2 = colFn colCertDiv_134_37_5.D2 (m := 5) from colCertDiv_134_37_5.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_37_5_match


theorem leaf_134_37_10 (hp : 10 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp)) T134_37
      hfix134_37 hinj134_37 hcardT134_37
      (fun i => conj_mem_of_fixedPoints _ _ (T134_37 i) (hfix134_37 i) _)
      ⟨134, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 10 hp) Q2.T134_37_2 Q2.hfix134_37_2 Q2.hinj134_37_2
      Q2.hcardT134_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_37_2 i) (Q2.hfix134_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 10 (transLenTr ⟨37, by decide⟩ 10 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T134_37 = colFn colCertDiv_134_37_10.D1 (m := 5) from colCertDiv_134_37_10.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 10 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T134_37_2 = colFn colCertDiv_134_37_10.D2 (m := 5) from colCertDiv_134_37_10.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_37_10_match


theorem leaf_134_37_15 (hp : 15 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp)) T134_37
      hfix134_37 hinj134_37 hcardT134_37
      (fun i => conj_mem_of_fixedPoints _ _ (T134_37 i) (hfix134_37 i) _)
      ⟨134, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 15 hp) Q2.T134_37_2 Q2.hfix134_37_2 Q2.hinj134_37_2
      Q2.hcardT134_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_37_2 i) (Q2.hfix134_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 15 (transLenTr ⟨37, by decide⟩ 15 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T134_37 = colFn colCertDiv_134_37_15.D1 (m := 5) from colCertDiv_134_37_15.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 15 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T134_37_2 = colFn colCertDiv_134_37_15.D2 (m := 5) from colCertDiv_134_37_15.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_37_15_match


theorem leaf_134_37_20 (hp : 20 < (Q2.transData.getD 37 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨37, by decide⟩ : Fin 148)) (colE2 ⟨37, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨37, by decide⟩ : Fin 148))
        (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨37, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp)) T134_37
      hfix134_37 hinj134_37 hcardT134_37
      (fun i => conj_mem_of_fixedPoints _ _ (T134_37 i) (hfix134_37 i) _)
      ⟨134, by decide⟩ ⟨37, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨37, by decide⟩ 20 hp) Q2.T134_37_2 Q2.hfix134_37_2 Q2.hinj134_37_2
      Q2.hcardT134_37_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_37_2 i) (Q2.hfix134_37_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨37, by decide⟩ 20 (transLenTr ⟨37, by decide⟩ 20 hp) : ↥(reps ⟨37, by decide⟩)) : Coordinate 1)
        T134_37 = colFn colCertDiv_134_37_20.D1 (m := 5) from colCertDiv_134_37_20.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨37, by decide⟩ 20 hp : ↥(Q2.reps ⟨37, by decide⟩)) : Coordinate 2)
        Q2.T134_37_2 = colFn colCertDiv_134_37_20.D2 (m := 5) from colCertDiv_134_37_20.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_37_20_match


theorem leaf_134_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T134_40
      hfix134_40 hinj134_40 hcardT134_40
      (fun i => conj_mem_of_fixedPoints _ _ (T134_40 i) (hfix134_40 i) _)
      ⟨134, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T134_40_2 Q2.hfix134_40_2 Q2.hinj134_40_2
      Q2.hcardT134_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_40_2 i) (Q2.hfix134_40_2 i) _)
      colCert_134_40_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T134_40
      hfix134_40 hinj134_40 hcardT134_40
      (fun i => conj_mem_of_fixedPoints _ _ (T134_40 i) (hfix134_40 i) _)
      ⟨134, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T134_40_2 Q2.hfix134_40_2 Q2.hinj134_40_2
      Q2.hcardT134_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_40_2 i) (Q2.hfix134_40_2 i) _)
      colCert_134_40_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T134_40
      hfix134_40 hinj134_40 hcardT134_40
      (fun i => conj_mem_of_fixedPoints _ _ (T134_40 i) (hfix134_40 i) _)
      ⟨134, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T134_40_2 Q2.hfix134_40_2 Q2.hinj134_40_2
      Q2.hcardT134_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_40_2 i) (Q2.hfix134_40_2 i) _)
      colCert_134_40_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T134_40
      hfix134_40 hinj134_40 hcardT134_40
      (fun i => conj_mem_of_fixedPoints _ _ (T134_40 i) (hfix134_40 i) _)
      ⟨134, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T134_40_2 Q2.hfix134_40_2 Q2.hinj134_40_2
      Q2.hcardT134_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_40_2 i) (Q2.hfix134_40_2 i) _)
      colCert_134_40_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T134_40
      hfix134_40 hinj134_40 hcardT134_40
      (fun i => conj_mem_of_fixedPoints _ _ (T134_40 i) (hfix134_40 i) _)
      ⟨134, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T134_40_2 Q2.hfix134_40_2 Q2.hinj134_40_2
      Q2.hcardT134_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_40_2 i) (Q2.hfix134_40_2 i) _)
      colCert_134_40_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T134_40
      hfix134_40 hinj134_40 hcardT134_40
      (fun i => conj_mem_of_fixedPoints _ _ (T134_40 i) (hfix134_40 i) _)
      ⟨134, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T134_40_2 Q2.hfix134_40_2 Q2.hinj134_40_2
      Q2.hcardT134_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_40_2 i) (Q2.hfix134_40_2 i) _)
      colCert_134_40_5.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T134_40
      hfix134_40 hinj134_40 hcardT134_40
      (fun i => conj_mem_of_fixedPoints _ _ (T134_40 i) (hfix134_40 i) _)
      ⟨134, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T134_40_2 Q2.hfix134_40_2 Q2.hinj134_40_2
      Q2.hcardT134_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_40_2 i) (Q2.hfix134_40_2 i) _)
      colCert_134_40_10.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T134_40
      hfix134_40 hinj134_40 hcardT134_40
      (fun i => conj_mem_of_fixedPoints _ _ (T134_40 i) (hfix134_40 i) _)
      ⟨134, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T134_40_2 Q2.hfix134_40_2 Q2.hinj134_40_2
      Q2.hcardT134_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_40_2 i) (Q2.hfix134_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T134_40 = colFn colCertDiv_134_40_15.D1 (m := 5) from colCertDiv_134_40_15.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T134_40_2 = colFn colCertDiv_134_40_15.D2 (m := 5) from colCertDiv_134_40_15.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_40_15_match


theorem leaf_134_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T134_40
      hfix134_40 hinj134_40 hcardT134_40
      (fun i => conj_mem_of_fixedPoints _ _ (T134_40 i) (hfix134_40 i) _)
      ⟨134, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T134_40_2 Q2.hfix134_40_2 Q2.hinj134_40_2
      Q2.hcardT134_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_40_2 i) (Q2.hfix134_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T134_40 = colFn colCertDiv_134_40_20.D1 (m := 5) from colCertDiv_134_40_20.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T134_40_2 = colFn colCertDiv_134_40_20.D2 (m := 5) from colCertDiv_134_40_20.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_40_20_match


theorem leaf_134_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T134_44
      hfix134_44 hinj134_44 hcardT134_44
      (fun i => conj_mem_of_fixedPoints _ _ (T134_44 i) (hfix134_44 i) _)
      ⟨134, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T134_44_2 Q2.hfix134_44_2 Q2.hinj134_44_2
      Q2.hcardT134_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_44_2 i) (Q2.hfix134_44_2 i) _)
      colCert_134_44_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T134_44
      hfix134_44 hinj134_44 hcardT134_44
      (fun i => conj_mem_of_fixedPoints _ _ (T134_44 i) (hfix134_44 i) _)
      ⟨134, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T134_44_2 Q2.hfix134_44_2 Q2.hinj134_44_2
      Q2.hcardT134_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_44_2 i) (Q2.hfix134_44_2 i) _)
      colCert_134_44_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T134_44
      hfix134_44 hinj134_44 hcardT134_44
      (fun i => conj_mem_of_fixedPoints _ _ (T134_44 i) (hfix134_44 i) _)
      ⟨134, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T134_44_2 Q2.hfix134_44_2 Q2.hinj134_44_2
      Q2.hcardT134_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_44_2 i) (Q2.hfix134_44_2 i) _)
      colCert_134_44_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T134_44
      hfix134_44 hinj134_44 hcardT134_44
      (fun i => conj_mem_of_fixedPoints _ _ (T134_44 i) (hfix134_44 i) _)
      ⟨134, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T134_44_2 Q2.hfix134_44_2 Q2.hinj134_44_2
      Q2.hcardT134_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_44_2 i) (Q2.hfix134_44_2 i) _)
      colCert_134_44_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T134_44
      hfix134_44 hinj134_44 hcardT134_44
      (fun i => conj_mem_of_fixedPoints _ _ (T134_44 i) (hfix134_44 i) _)
      ⟨134, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T134_44_2 Q2.hfix134_44_2 Q2.hinj134_44_2
      Q2.hcardT134_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_44_2 i) (Q2.hfix134_44_2 i) _)
      colCert_134_44_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T134_44
      hfix134_44 hinj134_44 hcardT134_44
      (fun i => conj_mem_of_fixedPoints _ _ (T134_44 i) (hfix134_44 i) _)
      ⟨134, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T134_44_2 Q2.hfix134_44_2 Q2.hinj134_44_2
      Q2.hcardT134_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_44_2 i) (Q2.hfix134_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T134_44 = colFn colCertDiv_134_44_5.D1 (m := 5) from colCertDiv_134_44_5.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 5 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T134_44_2 = colFn colCertDiv_134_44_5.D2 (m := 5) from colCertDiv_134_44_5.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_44_5_match


theorem leaf_134_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T134_44
      hfix134_44 hinj134_44 hcardT134_44
      (fun i => conj_mem_of_fixedPoints _ _ (T134_44 i) (hfix134_44 i) _)
      ⟨134, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T134_44_2 Q2.hfix134_44_2 Q2.hinj134_44_2
      Q2.hcardT134_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_44_2 i) (Q2.hfix134_44_2 i) _)
      colCert_134_44_10.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T134_44
      hfix134_44 hinj134_44 hcardT134_44
      (fun i => conj_mem_of_fixedPoints _ _ (T134_44 i) (hfix134_44 i) _)
      ⟨134, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T134_44_2 Q2.hfix134_44_2 Q2.hinj134_44_2
      Q2.hcardT134_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_44_2 i) (Q2.hfix134_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T134_44 = colFn colCertDiv_134_44_15.D1 (m := 5) from colCertDiv_134_44_15.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 15 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T134_44_2 = colFn colCertDiv_134_44_15.D2 (m := 5) from colCertDiv_134_44_15.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_44_15_match


theorem leaf_134_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T134_44
      hfix134_44 hinj134_44 hcardT134_44
      (fun i => conj_mem_of_fixedPoints _ _ (T134_44 i) (hfix134_44 i) _)
      ⟨134, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T134_44_2 Q2.hfix134_44_2 Q2.hinj134_44_2
      Q2.hcardT134_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_44_2 i) (Q2.hfix134_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T134_44 = colFn colCertDiv_134_44_20.D1 (m := 5) from colCertDiv_134_44_20.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 20 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T134_44_2 = colFn colCertDiv_134_44_20.D2 (m := 5) from colCertDiv_134_44_20.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_44_20_match


theorem leaf_134_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T134_51
      hfix134_51 hinj134_51 hcardT134_51
      (fun i => conj_mem_of_fixedPoints _ _ (T134_51 i) (hfix134_51 i) _)
      ⟨134, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T134_51_2 Q2.hfix134_51_2 Q2.hinj134_51_2
      Q2.hcardT134_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_51_2 i) (Q2.hfix134_51_2 i) _)
      colCert_134_51_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T134_51
      hfix134_51 hinj134_51 hcardT134_51
      (fun i => conj_mem_of_fixedPoints _ _ (T134_51 i) (hfix134_51 i) _)
      ⟨134, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T134_51_2 Q2.hfix134_51_2 Q2.hinj134_51_2
      Q2.hcardT134_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_51_2 i) (Q2.hfix134_51_2 i) _)
      colCert_134_51_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T134_51
      hfix134_51 hinj134_51 hcardT134_51
      (fun i => conj_mem_of_fixedPoints _ _ (T134_51 i) (hfix134_51 i) _)
      ⟨134, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T134_51_2 Q2.hfix134_51_2 Q2.hinj134_51_2
      Q2.hcardT134_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_51_2 i) (Q2.hfix134_51_2 i) _)
      colCert_134_51_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T134_51
      hfix134_51 hinj134_51 hcardT134_51
      (fun i => conj_mem_of_fixedPoints _ _ (T134_51 i) (hfix134_51 i) _)
      ⟨134, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T134_51_2 Q2.hfix134_51_2 Q2.hinj134_51_2
      Q2.hcardT134_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_51_2 i) (Q2.hfix134_51_2 i) _)
      colCert_134_51_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T134_51
      hfix134_51 hinj134_51 hcardT134_51
      (fun i => conj_mem_of_fixedPoints _ _ (T134_51 i) (hfix134_51 i) _)
      ⟨134, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T134_51_2 Q2.hfix134_51_2 Q2.hinj134_51_2
      Q2.hcardT134_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_51_2 i) (Q2.hfix134_51_2 i) _)
      colCert_134_51_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T134_51
      hfix134_51 hinj134_51 hcardT134_51
      (fun i => conj_mem_of_fixedPoints _ _ (T134_51 i) (hfix134_51 i) _)
      ⟨134, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T134_51_2 Q2.hfix134_51_2 Q2.hinj134_51_2
      Q2.hcardT134_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_51_2 i) (Q2.hfix134_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T134_51 = colFn colCertDiv_134_51_5.D1 (m := 5) from colCertDiv_134_51_5.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T134_51_2 = colFn colCertDiv_134_51_5.D2 (m := 5) from colCertDiv_134_51_5.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_51_5_match


theorem leaf_134_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T134_51
      hfix134_51 hinj134_51 hcardT134_51
      (fun i => conj_mem_of_fixedPoints _ _ (T134_51 i) (hfix134_51 i) _)
      ⟨134, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T134_51_2 Q2.hfix134_51_2 Q2.hinj134_51_2
      Q2.hcardT134_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_51_2 i) (Q2.hfix134_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T134_51 = colFn colCertDiv_134_51_10.D1 (m := 5) from colCertDiv_134_51_10.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T134_51_2 = colFn colCertDiv_134_51_10.D2 (m := 5) from colCertDiv_134_51_10.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_51_10_match


theorem leaf_134_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T134_51
      hfix134_51 hinj134_51 hcardT134_51
      (fun i => conj_mem_of_fixedPoints _ _ (T134_51 i) (hfix134_51 i) _)
      ⟨134, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T134_51_2 Q2.hfix134_51_2 Q2.hinj134_51_2
      Q2.hcardT134_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_51_2 i) (Q2.hfix134_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T134_51 = colFn colCertDiv_134_51_15.D1 (m := 5) from colCertDiv_134_51_15.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T134_51_2 = colFn colCertDiv_134_51_15.D2 (m := 5) from colCertDiv_134_51_15.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_51_15_match


theorem leaf_134_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T134_51
      hfix134_51 hinj134_51 hcardT134_51
      (fun i => conj_mem_of_fixedPoints _ _ (T134_51 i) (hfix134_51 i) _)
      ⟨134, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T134_51_2 Q2.hfix134_51_2 Q2.hinj134_51_2
      Q2.hcardT134_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_51_2 i) (Q2.hfix134_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T134_51 = colFn colCertDiv_134_51_20.D1 (m := 5) from colCertDiv_134_51_20.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T134_51_2 = colFn colCertDiv_134_51_20.D2 (m := 5) from colCertDiv_134_51_20.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_51_20_match


theorem leaf_134_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T134_53
      hfix134_53 hinj134_53 hcardT134_53
      (fun i => conj_mem_of_fixedPoints _ _ (T134_53 i) (hfix134_53 i) _)
      ⟨134, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T134_53_2 Q2.hfix134_53_2 Q2.hinj134_53_2
      Q2.hcardT134_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_53_2 i) (Q2.hfix134_53_2 i) _)
      colCert_134_53_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T134_53
      hfix134_53 hinj134_53 hcardT134_53
      (fun i => conj_mem_of_fixedPoints _ _ (T134_53 i) (hfix134_53 i) _)
      ⟨134, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T134_53_2 Q2.hfix134_53_2 Q2.hinj134_53_2
      Q2.hcardT134_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_53_2 i) (Q2.hfix134_53_2 i) _)
      colCert_134_53_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T134_53
      hfix134_53 hinj134_53 hcardT134_53
      (fun i => conj_mem_of_fixedPoints _ _ (T134_53 i) (hfix134_53 i) _)
      ⟨134, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T134_53_2 Q2.hfix134_53_2 Q2.hinj134_53_2
      Q2.hcardT134_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_53_2 i) (Q2.hfix134_53_2 i) _)
      colCert_134_53_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T134_53
      hfix134_53 hinj134_53 hcardT134_53
      (fun i => conj_mem_of_fixedPoints _ _ (T134_53 i) (hfix134_53 i) _)
      ⟨134, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T134_53_2 Q2.hfix134_53_2 Q2.hinj134_53_2
      Q2.hcardT134_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_53_2 i) (Q2.hfix134_53_2 i) _)
      colCert_134_53_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T134_53
      hfix134_53 hinj134_53 hcardT134_53
      (fun i => conj_mem_of_fixedPoints _ _ (T134_53 i) (hfix134_53 i) _)
      ⟨134, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T134_53_2 Q2.hfix134_53_2 Q2.hinj134_53_2
      Q2.hcardT134_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_53_2 i) (Q2.hfix134_53_2 i) _)
      colCert_134_53_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T134_53
      hfix134_53 hinj134_53 hcardT134_53
      (fun i => conj_mem_of_fixedPoints _ _ (T134_53 i) (hfix134_53 i) _)
      ⟨134, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T134_53_2 Q2.hfix134_53_2 Q2.hinj134_53_2
      Q2.hcardT134_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_53_2 i) (Q2.hfix134_53_2 i) _)
      colCert_134_53_5.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T134_53
      hfix134_53 hinj134_53 hcardT134_53
      (fun i => conj_mem_of_fixedPoints _ _ (T134_53 i) (hfix134_53 i) _)
      ⟨134, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T134_53_2 Q2.hfix134_53_2 Q2.hinj134_53_2
      Q2.hcardT134_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_53_2 i) (Q2.hfix134_53_2 i) _)
      colCert_134_53_10.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T134_53
      hfix134_53 hinj134_53 hcardT134_53
      (fun i => conj_mem_of_fixedPoints _ _ (T134_53 i) (hfix134_53 i) _)
      ⟨134, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T134_53_2 Q2.hfix134_53_2 Q2.hinj134_53_2
      Q2.hcardT134_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_53_2 i) (Q2.hfix134_53_2 i) _)
      colCert_134_53_15.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T134_53
      hfix134_53 hinj134_53 hcardT134_53
      (fun i => conj_mem_of_fixedPoints _ _ (T134_53 i) (hfix134_53 i) _)
      ⟨134, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T134_53_2 Q2.hfix134_53_2 Q2.hinj134_53_2
      Q2.hcardT134_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_53_2 i) (Q2.hfix134_53_2 i) _)
      colCert_134_53_20.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_83_0 (hp : 0 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp)) T134_83
      hfix134_83 hinj134_83 hcardT134_83
      (fun i => conj_mem_of_fixedPoints _ _ (T134_83 i) (hfix134_83 i) _)
      ⟨134, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 0 hp) Q2.T134_83_2 Q2.hfix134_83_2 Q2.hinj134_83_2
      Q2.hcardT134_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_83_2 i) (Q2.hfix134_83_2 i) _)
      colCert_134_83_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_83_1 (hp : 1 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp)) T134_83
      hfix134_83 hinj134_83 hcardT134_83
      (fun i => conj_mem_of_fixedPoints _ _ (T134_83 i) (hfix134_83 i) _)
      ⟨134, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 1 hp) Q2.T134_83_2 Q2.hfix134_83_2 Q2.hinj134_83_2
      Q2.hcardT134_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_83_2 i) (Q2.hfix134_83_2 i) _)
      colCert_134_83_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_83_2 (hp : 2 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp)) T134_83
      hfix134_83 hinj134_83 hcardT134_83
      (fun i => conj_mem_of_fixedPoints _ _ (T134_83 i) (hfix134_83 i) _)
      ⟨134, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 2 hp) Q2.T134_83_2 Q2.hfix134_83_2 Q2.hinj134_83_2
      Q2.hcardT134_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_83_2 i) (Q2.hfix134_83_2 i) _)
      colCert_134_83_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_83_3 (hp : 3 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp)) T134_83
      hfix134_83 hinj134_83 hcardT134_83
      (fun i => conj_mem_of_fixedPoints _ _ (T134_83 i) (hfix134_83 i) _)
      ⟨134, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 3 hp) Q2.T134_83_2 Q2.hfix134_83_2 Q2.hinj134_83_2
      Q2.hcardT134_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_83_2 i) (Q2.hfix134_83_2 i) _)
      colCert_134_83_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_83_4 (hp : 4 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp)) T134_83
      hfix134_83 hinj134_83 hcardT134_83
      (fun i => conj_mem_of_fixedPoints _ _ (T134_83 i) (hfix134_83 i) _)
      ⟨134, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 4 hp) Q2.T134_83_2 Q2.hfix134_83_2 Q2.hinj134_83_2
      Q2.hcardT134_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_83_2 i) (Q2.hfix134_83_2 i) _)
      colCert_134_83_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_83_5 (hp : 5 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp)) T134_83
      hfix134_83 hinj134_83 hcardT134_83
      (fun i => conj_mem_of_fixedPoints _ _ (T134_83 i) (hfix134_83 i) _)
      ⟨134, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 5 hp) Q2.T134_83_2 Q2.hfix134_83_2 Q2.hinj134_83_2
      Q2.hcardT134_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_83_2 i) (Q2.hfix134_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T134_83 = colFn colCertDiv_134_83_5.D1 (m := 5) from colCertDiv_134_83_5.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 5 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T134_83_2 = colFn colCertDiv_134_83_5.D2 (m := 5) from colCertDiv_134_83_5.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_83_5_match


theorem leaf_134_83_10 (hp : 10 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp)) T134_83
      hfix134_83 hinj134_83 hcardT134_83
      (fun i => conj_mem_of_fixedPoints _ _ (T134_83 i) (hfix134_83 i) _)
      ⟨134, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 10 hp) Q2.T134_83_2 Q2.hfix134_83_2 Q2.hinj134_83_2
      Q2.hcardT134_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_83_2 i) (Q2.hfix134_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T134_83 = colFn colCertDiv_134_83_10.D1 (m := 5) from colCertDiv_134_83_10.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 10 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T134_83_2 = colFn colCertDiv_134_83_10.D2 (m := 5) from colCertDiv_134_83_10.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_83_10_match


theorem leaf_134_83_15 (hp : 15 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp)) T134_83
      hfix134_83 hinj134_83 hcardT134_83
      (fun i => conj_mem_of_fixedPoints _ _ (T134_83 i) (hfix134_83 i) _)
      ⟨134, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 15 hp) Q2.T134_83_2 Q2.hfix134_83_2 Q2.hinj134_83_2
      Q2.hcardT134_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_83_2 i) (Q2.hfix134_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T134_83 = colFn colCertDiv_134_83_15.D1 (m := 5) from colCertDiv_134_83_15.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 15 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T134_83_2 = colFn colCertDiv_134_83_15.D2 (m := 5) from colCertDiv_134_83_15.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_83_15_match


theorem leaf_134_83_20 (hp : 20 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp)) T134_83
      hfix134_83 hinj134_83 hcardT134_83
      (fun i => conj_mem_of_fixedPoints _ _ (T134_83 i) (hfix134_83 i) _)
      ⟨134, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 20 hp) Q2.T134_83_2 Q2.hfix134_83_2 Q2.hinj134_83_2
      Q2.hcardT134_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_83_2 i) (Q2.hfix134_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T134_83 = colFn colCertDiv_134_83_20.D1 (m := 5) from colCertDiv_134_83_20.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 20 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T134_83_2 = colFn colCertDiv_134_83_20.D2 (m := 5) from colCertDiv_134_83_20.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_83_20_match


theorem leaf_134_90_0 (hp : 0 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 0 (transLenTr ⟨90, by decide⟩ 0 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 0 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      colCert_134_90_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_90_1 (hp : 1 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 1 (transLenTr ⟨90, by decide⟩ 1 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 1 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      colCert_134_90_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_90_2 (hp : 2 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 2 (transLenTr ⟨90, by decide⟩ 2 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 2 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      colCert_134_90_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_90_3 (hp : 3 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 3 (transLenTr ⟨90, by decide⟩ 3 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 3 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      colCert_134_90_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_90_4 (hp : 4 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 4 (transLenTr ⟨90, by decide⟩ 4 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 4 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      colCert_134_90_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_90_5 (hp : 5 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 5 (transLenTr ⟨90, by decide⟩ 5 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 5 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      colCert_134_90_5.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_90_10 (hp : 10 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 10 (transLenTr ⟨90, by decide⟩ 10 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 10 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      colCert_134_90_10.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_90_15 (hp : 15 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 15 (transLenTr ⟨90, by decide⟩ 15 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 15 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      colCert_134_90_15.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_90_20 (hp : 20 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 20 (transLenTr ⟨90, by decide⟩ 20 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 20 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      colCert_134_90_20.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_90_25 (hp : 25 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 25 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 25 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 25 (transLenTr ⟨90, by decide⟩ 25 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T134_90 = colFn colCertDiv_134_90_25.D1 (m := 5) from colCertDiv_134_90_25.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 25 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T134_90_2 = colFn colCertDiv_134_90_25.D2 (m := 5) from colCertDiv_134_90_25.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_90_25_match


theorem leaf_134_90_50 (hp : 50 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 50 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 50 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 50 (transLenTr ⟨90, by decide⟩ 50 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T134_90 = colFn colCertDiv_134_90_50.D1 (m := 5) from colCertDiv_134_90_50.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 50 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T134_90_2 = colFn colCertDiv_134_90_50.D2 (m := 5) from colCertDiv_134_90_50.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_90_50_match


theorem leaf_134_90_75 (hp : 75 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 75 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 75 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 75 (transLenTr ⟨90, by decide⟩ 75 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T134_90 = colFn colCertDiv_134_90_75.D1 (m := 5) from colCertDiv_134_90_75.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 75 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T134_90_2 = colFn colCertDiv_134_90_75.D2 (m := 5) from colCertDiv_134_90_75.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_90_75_match


theorem leaf_134_90_100 (hp : 100 < (Q2.transData.getD 90 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨90, by decide⟩ : Fin 148)) (colE2 ⟨90, by decide⟩ 100 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨90, by decide⟩ : Fin 148))
        (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨90, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp)) T134_90
      hfix134_90 hinj134_90 hcardT134_90
      (fun i => conj_mem_of_fixedPoints _ _ (T134_90 i) (hfix134_90 i) _)
      ⟨134, by decide⟩ ⟨90, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨90, by decide⟩ 100 hp) Q2.T134_90_2 Q2.hfix134_90_2 Q2.hinj134_90_2
      Q2.hcardT134_90_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_90_2 i) (Q2.hfix134_90_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨90, by decide⟩ 100 (transLenTr ⟨90, by decide⟩ 100 hp) : ↥(reps ⟨90, by decide⟩)) : Coordinate 1)
        T134_90 = colFn colCertDiv_134_90_100.D1 (m := 5) from colCertDiv_134_90_100.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨90, by decide⟩ 100 hp : ↥(Q2.reps ⟨90, by decide⟩)) : Coordinate 2)
        Q2.T134_90_2 = colFn colCertDiv_134_90_100.D2 (m := 5) from colCertDiv_134_90_100.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_90_100_match


theorem leaf_134_99_0 (hp : 0 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 0 (transLenTr ⟨99, by decide⟩ 0 hp)) T134_99
      hfix134_99 hinj134_99 hcardT134_99
      (fun i => conj_mem_of_fixedPoints _ _ (T134_99 i) (hfix134_99 i) _)
      ⟨134, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 0 hp) Q2.T134_99_2 Q2.hfix134_99_2 Q2.hinj134_99_2
      Q2.hcardT134_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_99_2 i) (Q2.hfix134_99_2 i) _)
      colCert_134_99_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_99_1 (hp : 1 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 1 (transLenTr ⟨99, by decide⟩ 1 hp)) T134_99
      hfix134_99 hinj134_99 hcardT134_99
      (fun i => conj_mem_of_fixedPoints _ _ (T134_99 i) (hfix134_99 i) _)
      ⟨134, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 1 hp) Q2.T134_99_2 Q2.hfix134_99_2 Q2.hinj134_99_2
      Q2.hcardT134_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_99_2 i) (Q2.hfix134_99_2 i) _)
      colCert_134_99_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_99_2 (hp : 2 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 2 (transLenTr ⟨99, by decide⟩ 2 hp)) T134_99
      hfix134_99 hinj134_99 hcardT134_99
      (fun i => conj_mem_of_fixedPoints _ _ (T134_99 i) (hfix134_99 i) _)
      ⟨134, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 2 hp) Q2.T134_99_2 Q2.hfix134_99_2 Q2.hinj134_99_2
      Q2.hcardT134_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_99_2 i) (Q2.hfix134_99_2 i) _)
      colCert_134_99_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_99_3 (hp : 3 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 3 (transLenTr ⟨99, by decide⟩ 3 hp)) T134_99
      hfix134_99 hinj134_99 hcardT134_99
      (fun i => conj_mem_of_fixedPoints _ _ (T134_99 i) (hfix134_99 i) _)
      ⟨134, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 3 hp) Q2.T134_99_2 Q2.hfix134_99_2 Q2.hinj134_99_2
      Q2.hcardT134_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_99_2 i) (Q2.hfix134_99_2 i) _)
      colCert_134_99_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_99_4 (hp : 4 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 4 (transLenTr ⟨99, by decide⟩ 4 hp)) T134_99
      hfix134_99 hinj134_99 hcardT134_99
      (fun i => conj_mem_of_fixedPoints _ _ (T134_99 i) (hfix134_99 i) _)
      ⟨134, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 4 hp) Q2.T134_99_2 Q2.hfix134_99_2 Q2.hinj134_99_2
      Q2.hcardT134_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_99_2 i) (Q2.hfix134_99_2 i) _)
      colCert_134_99_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_99_5 (hp : 5 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp)) T134_99
      hfix134_99 hinj134_99 hcardT134_99
      (fun i => conj_mem_of_fixedPoints _ _ (T134_99 i) (hfix134_99 i) _)
      ⟨134, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 5 hp) Q2.T134_99_2 Q2.hfix134_99_2 Q2.hinj134_99_2
      Q2.hcardT134_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_99_2 i) (Q2.hfix134_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 5 (transLenTr ⟨99, by decide⟩ 5 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T134_99 = colFn colCertDiv_134_99_5.D1 (m := 5) from colCertDiv_134_99_5.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 5 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T134_99_2 = colFn colCertDiv_134_99_5.D2 (m := 5) from colCertDiv_134_99_5.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_99_5_match


theorem leaf_134_99_10 (hp : 10 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp)) T134_99
      hfix134_99 hinj134_99 hcardT134_99
      (fun i => conj_mem_of_fixedPoints _ _ (T134_99 i) (hfix134_99 i) _)
      ⟨134, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 10 hp) Q2.T134_99_2 Q2.hfix134_99_2 Q2.hinj134_99_2
      Q2.hcardT134_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_99_2 i) (Q2.hfix134_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 10 (transLenTr ⟨99, by decide⟩ 10 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T134_99 = colFn colCertDiv_134_99_10.D1 (m := 5) from colCertDiv_134_99_10.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 10 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T134_99_2 = colFn colCertDiv_134_99_10.D2 (m := 5) from colCertDiv_134_99_10.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_99_10_match


theorem leaf_134_99_15 (hp : 15 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp)) T134_99
      hfix134_99 hinj134_99 hcardT134_99
      (fun i => conj_mem_of_fixedPoints _ _ (T134_99 i) (hfix134_99 i) _)
      ⟨134, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 15 hp) Q2.T134_99_2 Q2.hfix134_99_2 Q2.hinj134_99_2
      Q2.hcardT134_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_99_2 i) (Q2.hfix134_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 15 (transLenTr ⟨99, by decide⟩ 15 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T134_99 = colFn colCertDiv_134_99_15.D1 (m := 5) from colCertDiv_134_99_15.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 15 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T134_99_2 = colFn colCertDiv_134_99_15.D2 (m := 5) from colCertDiv_134_99_15.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_99_15_match


theorem leaf_134_99_20 (hp : 20 < (Q2.transData.getD 99 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨99, by decide⟩ : Fin 148)) (colE2 ⟨99, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨99, by decide⟩ : Fin 148))
        (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨99, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp)) T134_99
      hfix134_99 hinj134_99 hcardT134_99
      (fun i => conj_mem_of_fixedPoints _ _ (T134_99 i) (hfix134_99 i) _)
      ⟨134, by decide⟩ ⟨99, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨99, by decide⟩ 20 hp) Q2.T134_99_2 Q2.hfix134_99_2 Q2.hinj134_99_2
      Q2.hcardT134_99_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_99_2 i) (Q2.hfix134_99_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨99, by decide⟩ 20 (transLenTr ⟨99, by decide⟩ 20 hp) : ↥(reps ⟨99, by decide⟩)) : Coordinate 1)
        T134_99 = colFn colCertDiv_134_99_20.D1 (m := 5) from colCertDiv_134_99_20.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨99, by decide⟩ 20 hp : ↥(Q2.reps ⟨99, by decide⟩)) : Coordinate 2)
        Q2.T134_99_2 = colFn colCertDiv_134_99_20.D2 (m := 5) from colCertDiv_134_99_20.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_99_20_match


theorem leaf_134_102_0 (hp : 0 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 0 (transLenTr ⟨102, by decide⟩ 0 hp)) T134_102
      hfix134_102 hinj134_102 hcardT134_102
      (fun i => conj_mem_of_fixedPoints _ _ (T134_102 i) (hfix134_102 i) _)
      ⟨134, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 0 hp) Q2.T134_102_2 Q2.hfix134_102_2 Q2.hinj134_102_2
      Q2.hcardT134_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_102_2 i) (Q2.hfix134_102_2 i) _)
      colCert_134_102_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_102_1 (hp : 1 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 1 (transLenTr ⟨102, by decide⟩ 1 hp)) T134_102
      hfix134_102 hinj134_102 hcardT134_102
      (fun i => conj_mem_of_fixedPoints _ _ (T134_102 i) (hfix134_102 i) _)
      ⟨134, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 1 hp) Q2.T134_102_2 Q2.hfix134_102_2 Q2.hinj134_102_2
      Q2.hcardT134_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_102_2 i) (Q2.hfix134_102_2 i) _)
      colCert_134_102_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_102_2 (hp : 2 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 2 (transLenTr ⟨102, by decide⟩ 2 hp)) T134_102
      hfix134_102 hinj134_102 hcardT134_102
      (fun i => conj_mem_of_fixedPoints _ _ (T134_102 i) (hfix134_102 i) _)
      ⟨134, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 2 hp) Q2.T134_102_2 Q2.hfix134_102_2 Q2.hinj134_102_2
      Q2.hcardT134_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_102_2 i) (Q2.hfix134_102_2 i) _)
      colCert_134_102_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_102_3 (hp : 3 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 3 (transLenTr ⟨102, by decide⟩ 3 hp)) T134_102
      hfix134_102 hinj134_102 hcardT134_102
      (fun i => conj_mem_of_fixedPoints _ _ (T134_102 i) (hfix134_102 i) _)
      ⟨134, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 3 hp) Q2.T134_102_2 Q2.hfix134_102_2 Q2.hinj134_102_2
      Q2.hcardT134_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_102_2 i) (Q2.hfix134_102_2 i) _)
      colCert_134_102_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_102_4 (hp : 4 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 4 (transLenTr ⟨102, by decide⟩ 4 hp)) T134_102
      hfix134_102 hinj134_102 hcardT134_102
      (fun i => conj_mem_of_fixedPoints _ _ (T134_102 i) (hfix134_102 i) _)
      ⟨134, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 4 hp) Q2.T134_102_2 Q2.hfix134_102_2 Q2.hinj134_102_2
      Q2.hcardT134_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_102_2 i) (Q2.hfix134_102_2 i) _)
      colCert_134_102_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_102_5 (hp : 5 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp)) T134_102
      hfix134_102 hinj134_102 hcardT134_102
      (fun i => conj_mem_of_fixedPoints _ _ (T134_102 i) (hfix134_102 i) _)
      ⟨134, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 5 hp) Q2.T134_102_2 Q2.hfix134_102_2 Q2.hinj134_102_2
      Q2.hcardT134_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_102_2 i) (Q2.hfix134_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 5 (transLenTr ⟨102, by decide⟩ 5 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T134_102 = colFn colCertDiv_134_102_5.D1 (m := 5) from colCertDiv_134_102_5.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 5 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T134_102_2 = colFn colCertDiv_134_102_5.D2 (m := 5) from colCertDiv_134_102_5.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_102_5_match


theorem leaf_134_102_10 (hp : 10 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp)) T134_102
      hfix134_102 hinj134_102 hcardT134_102
      (fun i => conj_mem_of_fixedPoints _ _ (T134_102 i) (hfix134_102 i) _)
      ⟨134, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 10 hp) Q2.T134_102_2 Q2.hfix134_102_2 Q2.hinj134_102_2
      Q2.hcardT134_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_102_2 i) (Q2.hfix134_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 10 (transLenTr ⟨102, by decide⟩ 10 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T134_102 = colFn colCertDiv_134_102_10.D1 (m := 5) from colCertDiv_134_102_10.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 10 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T134_102_2 = colFn colCertDiv_134_102_10.D2 (m := 5) from colCertDiv_134_102_10.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_102_10_match


theorem leaf_134_102_15 (hp : 15 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 15 (transLenTr ⟨102, by decide⟩ 15 hp)) T134_102
      hfix134_102 hinj134_102 hcardT134_102
      (fun i => conj_mem_of_fixedPoints _ _ (T134_102 i) (hfix134_102 i) _)
      ⟨134, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 15 hp) Q2.T134_102_2 Q2.hfix134_102_2 Q2.hinj134_102_2
      Q2.hcardT134_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_102_2 i) (Q2.hfix134_102_2 i) _)
      colCert_134_102_15.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_102_20 (hp : 20 < (Q2.transData.getD 102 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨102, by decide⟩ : Fin 148)) (colE2 ⟨102, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨102, by decide⟩ : Fin 148))
        (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨102, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp)) T134_102
      hfix134_102 hinj134_102 hcardT134_102
      (fun i => conj_mem_of_fixedPoints _ _ (T134_102 i) (hfix134_102 i) _)
      ⟨134, by decide⟩ ⟨102, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨102, by decide⟩ 20 hp) Q2.T134_102_2 Q2.hfix134_102_2 Q2.hinj134_102_2
      Q2.hcardT134_102_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_102_2 i) (Q2.hfix134_102_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨102, by decide⟩ 20 (transLenTr ⟨102, by decide⟩ 20 hp) : ↥(reps ⟨102, by decide⟩)) : Coordinate 1)
        T134_102 = colFn colCertDiv_134_102_20.D1 (m := 5) from colCertDiv_134_102_20.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨102, by decide⟩ 20 hp : ↥(Q2.reps ⟨102, by decide⟩)) : Coordinate 2)
        Q2.T134_102_2 = colFn colCertDiv_134_102_20.D2 (m := 5) from colCertDiv_134_102_20.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_102_20_match


theorem leaf_134_106_0 (hp : 0 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp)) T134_106
      hfix134_106 hinj134_106 hcardT134_106
      (fun i => conj_mem_of_fixedPoints _ _ (T134_106 i) (hfix134_106 i) _)
      ⟨134, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 0 hp) Q2.T134_106_2 Q2.hfix134_106_2 Q2.hinj134_106_2
      Q2.hcardT134_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_106_2 i) (Q2.hfix134_106_2 i) _)
      colCert_134_106_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_106_1 (hp : 1 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp)) T134_106
      hfix134_106 hinj134_106 hcardT134_106
      (fun i => conj_mem_of_fixedPoints _ _ (T134_106 i) (hfix134_106 i) _)
      ⟨134, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 1 hp) Q2.T134_106_2 Q2.hfix134_106_2 Q2.hinj134_106_2
      Q2.hcardT134_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_106_2 i) (Q2.hfix134_106_2 i) _)
      colCert_134_106_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_106_2 (hp : 2 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp)) T134_106
      hfix134_106 hinj134_106 hcardT134_106
      (fun i => conj_mem_of_fixedPoints _ _ (T134_106 i) (hfix134_106 i) _)
      ⟨134, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 2 hp) Q2.T134_106_2 Q2.hfix134_106_2 Q2.hinj134_106_2
      Q2.hcardT134_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_106_2 i) (Q2.hfix134_106_2 i) _)
      colCert_134_106_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_106_3 (hp : 3 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp)) T134_106
      hfix134_106 hinj134_106 hcardT134_106
      (fun i => conj_mem_of_fixedPoints _ _ (T134_106 i) (hfix134_106 i) _)
      ⟨134, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 3 hp) Q2.T134_106_2 Q2.hfix134_106_2 Q2.hinj134_106_2
      Q2.hcardT134_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_106_2 i) (Q2.hfix134_106_2 i) _)
      colCert_134_106_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_106_4 (hp : 4 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp)) T134_106
      hfix134_106 hinj134_106 hcardT134_106
      (fun i => conj_mem_of_fixedPoints _ _ (T134_106 i) (hfix134_106 i) _)
      ⟨134, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 4 hp) Q2.T134_106_2 Q2.hfix134_106_2 Q2.hinj134_106_2
      Q2.hcardT134_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_106_2 i) (Q2.hfix134_106_2 i) _)
      colCert_134_106_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_106_5 (hp : 5 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp)) T134_106
      hfix134_106 hinj134_106 hcardT134_106
      (fun i => conj_mem_of_fixedPoints _ _ (T134_106 i) (hfix134_106 i) _)
      ⟨134, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 5 hp) Q2.T134_106_2 Q2.hfix134_106_2 Q2.hinj134_106_2
      Q2.hcardT134_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_106_2 i) (Q2.hfix134_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T134_106 = colFn colCertDiv_134_106_5.D1 (m := 5) from colCertDiv_134_106_5.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 5 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T134_106_2 = colFn colCertDiv_134_106_5.D2 (m := 5) from colCertDiv_134_106_5.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_106_5_match


theorem leaf_134_106_10 (hp : 10 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp)) T134_106
      hfix134_106 hinj134_106 hcardT134_106
      (fun i => conj_mem_of_fixedPoints _ _ (T134_106 i) (hfix134_106 i) _)
      ⟨134, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 10 hp) Q2.T134_106_2 Q2.hfix134_106_2 Q2.hinj134_106_2
      Q2.hcardT134_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_106_2 i) (Q2.hfix134_106_2 i) _)
      colCert_134_106_10.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_106_15 (hp : 15 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp)) T134_106
      hfix134_106 hinj134_106 hcardT134_106
      (fun i => conj_mem_of_fixedPoints _ _ (T134_106 i) (hfix134_106 i) _)
      ⟨134, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 15 hp) Q2.T134_106_2 Q2.hfix134_106_2 Q2.hinj134_106_2
      Q2.hcardT134_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_106_2 i) (Q2.hfix134_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T134_106 = colFn colCertDiv_134_106_15.D1 (m := 5) from colCertDiv_134_106_15.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 15 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T134_106_2 = colFn colCertDiv_134_106_15.D2 (m := 5) from colCertDiv_134_106_15.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_106_15_match


theorem leaf_134_106_20 (hp : 20 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp)) T134_106
      hfix134_106 hinj134_106 hcardT134_106
      (fun i => conj_mem_of_fixedPoints _ _ (T134_106 i) (hfix134_106 i) _)
      ⟨134, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 20 hp) Q2.T134_106_2 Q2.hfix134_106_2 Q2.hinj134_106_2
      Q2.hcardT134_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_106_2 i) (Q2.hfix134_106_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp) : ↥(reps ⟨106, by decide⟩)) : Coordinate 1)
        T134_106 = colFn colCertDiv_134_106_20.D1 (m := 5) from colCertDiv_134_106_20.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨106, by decide⟩ 20 hp : ↥(Q2.reps ⟨106, by decide⟩)) : Coordinate 2)
        Q2.T134_106_2 = colFn colCertDiv_134_106_20.D2 (m := 5) from colCertDiv_134_106_20.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_106_20_match


theorem leaf_134_113_0 (hp : 0 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 0 (transLenTr ⟨113, by decide⟩ 0 hp)) T134_113
      hfix134_113 hinj134_113 hcardT134_113
      (fun i => conj_mem_of_fixedPoints _ _ (T134_113 i) (hfix134_113 i) _)
      ⟨134, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 0 hp) Q2.T134_113_2 Q2.hfix134_113_2 Q2.hinj134_113_2
      Q2.hcardT134_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_113_2 i) (Q2.hfix134_113_2 i) _)
      colCert_134_113_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_113_1 (hp : 1 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 1 (transLenTr ⟨113, by decide⟩ 1 hp)) T134_113
      hfix134_113 hinj134_113 hcardT134_113
      (fun i => conj_mem_of_fixedPoints _ _ (T134_113 i) (hfix134_113 i) _)
      ⟨134, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 1 hp) Q2.T134_113_2 Q2.hfix134_113_2 Q2.hinj134_113_2
      Q2.hcardT134_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_113_2 i) (Q2.hfix134_113_2 i) _)
      colCert_134_113_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_113_2 (hp : 2 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 2 (transLenTr ⟨113, by decide⟩ 2 hp)) T134_113
      hfix134_113 hinj134_113 hcardT134_113
      (fun i => conj_mem_of_fixedPoints _ _ (T134_113 i) (hfix134_113 i) _)
      ⟨134, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 2 hp) Q2.T134_113_2 Q2.hfix134_113_2 Q2.hinj134_113_2
      Q2.hcardT134_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_113_2 i) (Q2.hfix134_113_2 i) _)
      colCert_134_113_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_113_3 (hp : 3 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 3 (transLenTr ⟨113, by decide⟩ 3 hp)) T134_113
      hfix134_113 hinj134_113 hcardT134_113
      (fun i => conj_mem_of_fixedPoints _ _ (T134_113 i) (hfix134_113 i) _)
      ⟨134, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 3 hp) Q2.T134_113_2 Q2.hfix134_113_2 Q2.hinj134_113_2
      Q2.hcardT134_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_113_2 i) (Q2.hfix134_113_2 i) _)
      colCert_134_113_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_113_4 (hp : 4 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 4 (transLenTr ⟨113, by decide⟩ 4 hp)) T134_113
      hfix134_113 hinj134_113 hcardT134_113
      (fun i => conj_mem_of_fixedPoints _ _ (T134_113 i) (hfix134_113 i) _)
      ⟨134, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 4 hp) Q2.T134_113_2 Q2.hfix134_113_2 Q2.hinj134_113_2
      Q2.hcardT134_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_113_2 i) (Q2.hfix134_113_2 i) _)
      colCert_134_113_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_113_5 (hp : 5 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 5 (transLenTr ⟨113, by decide⟩ 5 hp)) T134_113
      hfix134_113 hinj134_113 hcardT134_113
      (fun i => conj_mem_of_fixedPoints _ _ (T134_113 i) (hfix134_113 i) _)
      ⟨134, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 5 hp) Q2.T134_113_2 Q2.hfix134_113_2 Q2.hinj134_113_2
      Q2.hcardT134_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_113_2 i) (Q2.hfix134_113_2 i) _)
      colCert_134_113_5.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_113_10 (hp : 10 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp)) T134_113
      hfix134_113 hinj134_113 hcardT134_113
      (fun i => conj_mem_of_fixedPoints _ _ (T134_113 i) (hfix134_113 i) _)
      ⟨134, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 10 hp) Q2.T134_113_2 Q2.hfix134_113_2 Q2.hinj134_113_2
      Q2.hcardT134_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_113_2 i) (Q2.hfix134_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 10 (transLenTr ⟨113, by decide⟩ 10 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T134_113 = colFn colCertDiv_134_113_10.D1 (m := 5) from colCertDiv_134_113_10.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 10 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T134_113_2 = colFn colCertDiv_134_113_10.D2 (m := 5) from colCertDiv_134_113_10.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_113_10_match


theorem leaf_134_113_15 (hp : 15 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp)) T134_113
      hfix134_113 hinj134_113 hcardT134_113
      (fun i => conj_mem_of_fixedPoints _ _ (T134_113 i) (hfix134_113 i) _)
      ⟨134, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 15 hp) Q2.T134_113_2 Q2.hfix134_113_2 Q2.hinj134_113_2
      Q2.hcardT134_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_113_2 i) (Q2.hfix134_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 15 (transLenTr ⟨113, by decide⟩ 15 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T134_113 = colFn colCertDiv_134_113_15.D1 (m := 5) from colCertDiv_134_113_15.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 15 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T134_113_2 = colFn colCertDiv_134_113_15.D2 (m := 5) from colCertDiv_134_113_15.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_113_15_match


theorem leaf_134_113_20 (hp : 20 < (Q2.transData.getD 113 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨113, by decide⟩ : Fin 148)) (colE2 ⟨113, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨113, by decide⟩ : Fin 148))
        (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨134, by decide⟩ : Fin 148) ⟨113, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp)) T134_113
      hfix134_113 hinj134_113 hcardT134_113
      (fun i => conj_mem_of_fixedPoints _ _ (T134_113 i) (hfix134_113 i) _)
      ⟨134, by decide⟩ ⟨113, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨113, by decide⟩ 20 hp) Q2.T134_113_2 Q2.hfix134_113_2 Q2.hinj134_113_2
      Q2.hcardT134_113_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_113_2 i) (Q2.hfix134_113_2 i) _)
      ?_).symm
  rw [show colData1 (⟨134, by decide⟩ : Fin 148)
        ((colE1 ⟨113, by decide⟩ 20 (transLenTr ⟨113, by decide⟩ 20 hp) : ↥(reps ⟨113, by decide⟩)) : Coordinate 1)
        T134_113 = colFn colCertDiv_134_113_20.D1 (m := 5) from colCertDiv_134_113_20.bind1,
    show colData2 (⟨134, by decide⟩ : Fin 148)
        ((colE2 ⟨113, by decide⟩ 20 hp : ↥(Q2.reps ⟨113, by decide⟩)) : Coordinate 2)
        Q2.T134_113_2 = colFn colCertDiv_134_113_20.D2 (m := 5) from colCertDiv_134_113_20.bind2]
  rw [alnId_134 j hj]
  exact fastcode_of_div ⟨134, by decide⟩ _ _ _
    ((alnId_134 j hj) ▸ Q2.listedAt (⟨134, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨134, by decide⟩ : Fin 148) hj hq).1) colCertDiv_134_113_20_match


theorem leaf_134_134_0 (hp : 0 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 0 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 0 (transLenTr ⟨134, by decide⟩ 0 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 0 (transLenTr ⟨134, by decide⟩ 0 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 0 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_0.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_1 (hp : 1 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 1 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 1 (transLenTr ⟨134, by decide⟩ 1 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 1 (transLenTr ⟨134, by decide⟩ 1 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 1 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_1.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_2 (hp : 2 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 2 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 2 (transLenTr ⟨134, by decide⟩ 2 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 2 (transLenTr ⟨134, by decide⟩ 2 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 2 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_2.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_3 (hp : 3 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 3 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 3 (transLenTr ⟨134, by decide⟩ 3 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 3 (transLenTr ⟨134, by decide⟩ 3 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 3 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_3.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_4 (hp : 4 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 4 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 4 (transLenTr ⟨134, by decide⟩ 4 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 4 (transLenTr ⟨134, by decide⟩ 4 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 4 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_4.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_5 (hp : 5 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 5 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 5 (transLenTr ⟨134, by decide⟩ 5 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 5 (transLenTr ⟨134, by decide⟩ 5 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 5 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_5.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_6 (hp : 6 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 6 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 6 (transLenTr ⟨134, by decide⟩ 6 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 6 (transLenTr ⟨134, by decide⟩ 6 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 6 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_6.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_7 (hp : 7 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 7 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 7 (transLenTr ⟨134, by decide⟩ 7 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 7 (transLenTr ⟨134, by decide⟩ 7 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 7 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_7.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_8 (hp : 8 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 8 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 8 (transLenTr ⟨134, by decide⟩ 8 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 8 (transLenTr ⟨134, by decide⟩ 8 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 8 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_8.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_9 (hp : 9 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 9 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 9 (transLenTr ⟨134, by decide⟩ 9 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 9 (transLenTr ⟨134, by decide⟩ 9 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 9 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_9.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_10 (hp : 10 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 10 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 10 (transLenTr ⟨134, by decide⟩ 10 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 10 (transLenTr ⟨134, by decide⟩ 10 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 10 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_10.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_11 (hp : 11 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 11 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 11 (transLenTr ⟨134, by decide⟩ 11 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 11 (transLenTr ⟨134, by decide⟩ 11 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 11 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_11.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_12 (hp : 12 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 12 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 12 (transLenTr ⟨134, by decide⟩ 12 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 12 (transLenTr ⟨134, by decide⟩ 12 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 12 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_12.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_13 (hp : 13 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 13 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 13 (transLenTr ⟨134, by decide⟩ 13 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 13 (transLenTr ⟨134, by decide⟩ 13 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 13 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_13.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_14 (hp : 14 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 14 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 14 (transLenTr ⟨134, by decide⟩ 14 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 14 (transLenTr ⟨134, by decide⟩ 14 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 14 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_14.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_15 (hp : 15 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 15 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 15 (transLenTr ⟨134, by decide⟩ 15 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 15 (transLenTr ⟨134, by decide⟩ 15 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 15 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_15.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_16 (hp : 16 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 16 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 16 (transLenTr ⟨134, by decide⟩ 16 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 16 (transLenTr ⟨134, by decide⟩ 16 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 16 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_16.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_17 (hp : 17 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 17 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 17 (transLenTr ⟨134, by decide⟩ 17 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 17 (transLenTr ⟨134, by decide⟩ 17 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 17 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_17.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_18 (hp : 18 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 18 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 18 (transLenTr ⟨134, by decide⟩ 18 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 18 (transLenTr ⟨134, by decide⟩ 18 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 18 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_18.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_19 (hp : 19 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 19 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 19 (transLenTr ⟨134, by decide⟩ 19 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 19 (transLenTr ⟨134, by decide⟩ 19 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 19 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_19.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_20 (hp : 20 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 20 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 20 (transLenTr ⟨134, by decide⟩ 20 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 20 (transLenTr ⟨134, by decide⟩ 20 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 20 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_20.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_21 (hp : 21 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 21 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 21 (transLenTr ⟨134, by decide⟩ 21 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 21 (transLenTr ⟨134, by decide⟩ 21 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 21 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_21.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_22 (hp : 22 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 22 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 22 (transLenTr ⟨134, by decide⟩ 22 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 22 (transLenTr ⟨134, by decide⟩ 22 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 22 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_22.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_23 (hp : 23 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 23 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 23 (transLenTr ⟨134, by decide⟩ 23 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 23 (transLenTr ⟨134, by decide⟩ 23 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 23 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_23.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_134_134_24 (hp : 24 < (Q2.transData.getD 134 []).length)
    (j : Nat) (hj : j < (repChars.getD 134 []).length)
    (hq : (normIsRep.getD 134 []).getD j false = true) :
    species (Q2.reps (⟨134, by decide⟩ : Fin 148)) (colE2 ⟨134, by decide⟩ 24 hp)
        (rowE2 (⟨134, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨134, by decide⟩ : Fin 148))
        (colE1 ⟨134, by decide⟩ 24 (transLenTr ⟨134, by decide⟩ 24 hp))
        (rowE1 (⟨134, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨134, by decide⟩ : Fin 148) ⟨134, by decide⟩ _
      (validAt ⟨134, by decide⟩ (listedAt ⟨134, by decide⟩ hj))
      (colE1 ⟨134, by decide⟩ 24 (transLenTr ⟨134, by decide⟩ 24 hp)) T134_134
      hfix134_134 hinj134_134 hcardT134_134
      (fun i => conj_mem_of_fixedPoints _ _ (T134_134 i) (hfix134_134 i) _)
      ⟨134, by decide⟩ ⟨134, by decide⟩ _
      (Q2.validAt ⟨134, by decide⟩ (Q2.listedAt ⟨134, by decide⟩
        (alnCheck_rep ⟨134, by decide⟩ hj hq).1))
      (colE2 ⟨134, by decide⟩ 24 hp) Q2.T134_134_2 Q2.hfix134_134_2 Q2.hinj134_134_2
      Q2.hcardT134_134_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T134_134_2 i) (Q2.hfix134_134_2 i) _)
      colCert_134_134_24.hD ?_).symm
  rw [alnId_134 j hj]


theorem leaf_135_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T135_4
      hfix135_4 hinj135_4 hcardT135_4
      (fun i => conj_mem_of_fixedPoints _ _ (T135_4 i) (hfix135_4 i) _)
      ⟨135, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T135_4_2 Q2.hfix135_4_2 Q2.hinj135_4_2
      Q2.hcardT135_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_4_2 i) (Q2.hfix135_4_2 i) _)
      colCert_135_4_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T135_4
      hfix135_4 hinj135_4 hcardT135_4
      (fun i => conj_mem_of_fixedPoints _ _ (T135_4 i) (hfix135_4 i) _)
      ⟨135, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T135_4_2 Q2.hfix135_4_2 Q2.hinj135_4_2
      Q2.hcardT135_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_4_2 i) (Q2.hfix135_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T135_4 = colFn colCertDiv_135_4_1.D1 (m := 5) from colCertDiv_135_4_1.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 1 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T135_4_2 = colFn colCertDiv_135_4_1.D2 (m := 5) from colCertDiv_135_4_1.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_4_1_match


theorem leaf_135_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T135_4
      hfix135_4 hinj135_4 hcardT135_4
      (fun i => conj_mem_of_fixedPoints _ _ (T135_4 i) (hfix135_4 i) _)
      ⟨135, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T135_4_2 Q2.hfix135_4_2 Q2.hinj135_4_2
      Q2.hcardT135_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_4_2 i) (Q2.hfix135_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T135_4 = colFn colCertDiv_135_4_2.D1 (m := 5) from colCertDiv_135_4_2.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 2 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T135_4_2 = colFn colCertDiv_135_4_2.D2 (m := 5) from colCertDiv_135_4_2.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_4_2_match


theorem leaf_135_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T135_4
      hfix135_4 hinj135_4 hcardT135_4
      (fun i => conj_mem_of_fixedPoints _ _ (T135_4 i) (hfix135_4 i) _)
      ⟨135, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T135_4_2 Q2.hfix135_4_2 Q2.hinj135_4_2
      Q2.hcardT135_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_4_2 i) (Q2.hfix135_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T135_4 = colFn colCertDiv_135_4_3.D1 (m := 5) from colCertDiv_135_4_3.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 3 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T135_4_2 = colFn colCertDiv_135_4_3.D2 (m := 5) from colCertDiv_135_4_3.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_4_3_match


theorem leaf_135_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T135_4
      hfix135_4 hinj135_4 hcardT135_4
      (fun i => conj_mem_of_fixedPoints _ _ (T135_4 i) (hfix135_4 i) _)
      ⟨135, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T135_4_2 Q2.hfix135_4_2 Q2.hinj135_4_2
      Q2.hcardT135_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_4_2 i) (Q2.hfix135_4_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp) : ↥(reps ⟨4, by decide⟩)) : Coordinate 1)
        T135_4 = colFn colCertDiv_135_4_4.D1 (m := 5) from colCertDiv_135_4_4.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨4, by decide⟩ 4 hp : ↥(Q2.reps ⟨4, by decide⟩)) : Coordinate 2)
        Q2.T135_4_2 = colFn colCertDiv_135_4_4.D2 (m := 5) from colCertDiv_135_4_4.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_4_4_match


theorem leaf_135_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T135_10
      hfix135_10 hinj135_10 hcardT135_10
      (fun i => conj_mem_of_fixedPoints _ _ (T135_10 i) (hfix135_10 i) _)
      ⟨135, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T135_10_2 Q2.hfix135_10_2 Q2.hinj135_10_2
      Q2.hcardT135_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_10_2 i) (Q2.hfix135_10_2 i) _)
      colCert_135_10_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T135_10
      hfix135_10 hinj135_10 hcardT135_10
      (fun i => conj_mem_of_fixedPoints _ _ (T135_10 i) (hfix135_10 i) _)
      ⟨135, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T135_10_2 Q2.hfix135_10_2 Q2.hinj135_10_2
      Q2.hcardT135_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_10_2 i) (Q2.hfix135_10_2 i) _)
      colCert_135_10_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T135_10
      hfix135_10 hinj135_10 hcardT135_10
      (fun i => conj_mem_of_fixedPoints _ _ (T135_10 i) (hfix135_10 i) _)
      ⟨135, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T135_10_2 Q2.hfix135_10_2 Q2.hinj135_10_2
      Q2.hcardT135_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_10_2 i) (Q2.hfix135_10_2 i) _)
      colCert_135_10_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T135_10
      hfix135_10 hinj135_10 hcardT135_10
      (fun i => conj_mem_of_fixedPoints _ _ (T135_10 i) (hfix135_10 i) _)
      ⟨135, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T135_10_2 Q2.hfix135_10_2 Q2.hinj135_10_2
      Q2.hcardT135_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_10_2 i) (Q2.hfix135_10_2 i) _)
      colCert_135_10_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T135_10
      hfix135_10 hinj135_10 hcardT135_10
      (fun i => conj_mem_of_fixedPoints _ _ (T135_10 i) (hfix135_10 i) _)
      ⟨135, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T135_10_2 Q2.hfix135_10_2 Q2.hinj135_10_2
      Q2.hcardT135_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_10_2 i) (Q2.hfix135_10_2 i) _)
      colCert_135_10_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T135_12
      hfix135_12 hinj135_12 hcardT135_12
      (fun i => conj_mem_of_fixedPoints _ _ (T135_12 i) (hfix135_12 i) _)
      ⟨135, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T135_12_2 Q2.hfix135_12_2 Q2.hinj135_12_2
      Q2.hcardT135_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_12_2 i) (Q2.hfix135_12_2 i) _)
      colCert_135_12_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T135_12
      hfix135_12 hinj135_12 hcardT135_12
      (fun i => conj_mem_of_fixedPoints _ _ (T135_12 i) (hfix135_12 i) _)
      ⟨135, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T135_12_2 Q2.hfix135_12_2 Q2.hinj135_12_2
      Q2.hcardT135_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_12_2 i) (Q2.hfix135_12_2 i) _)
      colCert_135_12_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T135_12
      hfix135_12 hinj135_12 hcardT135_12
      (fun i => conj_mem_of_fixedPoints _ _ (T135_12 i) (hfix135_12 i) _)
      ⟨135, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T135_12_2 Q2.hfix135_12_2 Q2.hinj135_12_2
      Q2.hcardT135_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_12_2 i) (Q2.hfix135_12_2 i) _)
      colCert_135_12_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T135_12
      hfix135_12 hinj135_12 hcardT135_12
      (fun i => conj_mem_of_fixedPoints _ _ (T135_12 i) (hfix135_12 i) _)
      ⟨135, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T135_12_2 Q2.hfix135_12_2 Q2.hinj135_12_2
      Q2.hcardT135_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_12_2 i) (Q2.hfix135_12_2 i) _)
      colCert_135_12_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T135_12
      hfix135_12 hinj135_12 hcardT135_12
      (fun i => conj_mem_of_fixedPoints _ _ (T135_12 i) (hfix135_12 i) _)
      ⟨135, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T135_12_2 Q2.hfix135_12_2 Q2.hinj135_12_2
      Q2.hcardT135_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_12_2 i) (Q2.hfix135_12_2 i) _)
      colCert_135_12_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T135_22
      hfix135_22 hinj135_22 hcardT135_22
      (fun i => conj_mem_of_fixedPoints _ _ (T135_22 i) (hfix135_22 i) _)
      ⟨135, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T135_22_2 Q2.hfix135_22_2 Q2.hinj135_22_2
      Q2.hcardT135_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_22_2 i) (Q2.hfix135_22_2 i) _)
      colCert_135_22_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T135_22
      hfix135_22 hinj135_22 hcardT135_22
      (fun i => conj_mem_of_fixedPoints _ _ (T135_22 i) (hfix135_22 i) _)
      ⟨135, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T135_22_2 Q2.hfix135_22_2 Q2.hinj135_22_2
      Q2.hcardT135_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_22_2 i) (Q2.hfix135_22_2 i) _)
      colCert_135_22_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T135_22
      hfix135_22 hinj135_22 hcardT135_22
      (fun i => conj_mem_of_fixedPoints _ _ (T135_22 i) (hfix135_22 i) _)
      ⟨135, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T135_22_2 Q2.hfix135_22_2 Q2.hinj135_22_2
      Q2.hcardT135_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_22_2 i) (Q2.hfix135_22_2 i) _)
      colCert_135_22_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T135_22
      hfix135_22 hinj135_22 hcardT135_22
      (fun i => conj_mem_of_fixedPoints _ _ (T135_22 i) (hfix135_22 i) _)
      ⟨135, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T135_22_2 Q2.hfix135_22_2 Q2.hinj135_22_2
      Q2.hcardT135_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_22_2 i) (Q2.hfix135_22_2 i) _)
      colCert_135_22_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T135_22
      hfix135_22 hinj135_22 hcardT135_22
      (fun i => conj_mem_of_fixedPoints _ _ (T135_22 i) (hfix135_22 i) _)
      ⟨135, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T135_22_2 Q2.hfix135_22_2 Q2.hinj135_22_2
      Q2.hcardT135_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_22_2 i) (Q2.hfix135_22_2 i) _)
      colCert_135_22_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T135_22
      hfix135_22 hinj135_22 hcardT135_22
      (fun i => conj_mem_of_fixedPoints _ _ (T135_22 i) (hfix135_22 i) _)
      ⟨135, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T135_22_2 Q2.hfix135_22_2 Q2.hinj135_22_2
      Q2.hcardT135_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_22_2 i) (Q2.hfix135_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T135_22 = colFn colCertDiv_135_22_5.D1 (m := 5) from colCertDiv_135_22_5.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 5 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T135_22_2 = colFn colCertDiv_135_22_5.D2 (m := 5) from colCertDiv_135_22_5.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_22_5_match


theorem leaf_135_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T135_22
      hfix135_22 hinj135_22 hcardT135_22
      (fun i => conj_mem_of_fixedPoints _ _ (T135_22 i) (hfix135_22 i) _)
      ⟨135, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T135_22_2 Q2.hfix135_22_2 Q2.hinj135_22_2
      Q2.hcardT135_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_22_2 i) (Q2.hfix135_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T135_22 = colFn colCertDiv_135_22_10.D1 (m := 5) from colCertDiv_135_22_10.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 10 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T135_22_2 = colFn colCertDiv_135_22_10.D2 (m := 5) from colCertDiv_135_22_10.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_22_10_match


theorem leaf_135_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T135_22
      hfix135_22 hinj135_22 hcardT135_22
      (fun i => conj_mem_of_fixedPoints _ _ (T135_22 i) (hfix135_22 i) _)
      ⟨135, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T135_22_2 Q2.hfix135_22_2 Q2.hinj135_22_2
      Q2.hcardT135_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_22_2 i) (Q2.hfix135_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T135_22 = colFn colCertDiv_135_22_15.D1 (m := 5) from colCertDiv_135_22_15.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 15 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T135_22_2 = colFn colCertDiv_135_22_15.D2 (m := 5) from colCertDiv_135_22_15.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_22_15_match


theorem leaf_135_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T135_22
      hfix135_22 hinj135_22 hcardT135_22
      (fun i => conj_mem_of_fixedPoints _ _ (T135_22 i) (hfix135_22 i) _)
      ⟨135, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T135_22_2 Q2.hfix135_22_2 Q2.hinj135_22_2
      Q2.hcardT135_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_22_2 i) (Q2.hfix135_22_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp) : ↥(reps ⟨22, by decide⟩)) : Coordinate 1)
        T135_22 = colFn colCertDiv_135_22_20.D1 (m := 5) from colCertDiv_135_22_20.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨22, by decide⟩ 20 hp : ↥(Q2.reps ⟨22, by decide⟩)) : Coordinate 2)
        Q2.T135_22_2 = colFn colCertDiv_135_22_20.D2 (m := 5) from colCertDiv_135_22_20.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_22_20_match


theorem leaf_135_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T135_29
      hfix135_29 hinj135_29 hcardT135_29
      (fun i => conj_mem_of_fixedPoints _ _ (T135_29 i) (hfix135_29 i) _)
      ⟨135, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T135_29_2 Q2.hfix135_29_2 Q2.hinj135_29_2
      Q2.hcardT135_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_29_2 i) (Q2.hfix135_29_2 i) _)
      colCert_135_29_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T135_29
      hfix135_29 hinj135_29 hcardT135_29
      (fun i => conj_mem_of_fixedPoints _ _ (T135_29 i) (hfix135_29 i) _)
      ⟨135, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T135_29_2 Q2.hfix135_29_2 Q2.hinj135_29_2
      Q2.hcardT135_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_29_2 i) (Q2.hfix135_29_2 i) _)
      colCert_135_29_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T135_29
      hfix135_29 hinj135_29 hcardT135_29
      (fun i => conj_mem_of_fixedPoints _ _ (T135_29 i) (hfix135_29 i) _)
      ⟨135, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T135_29_2 Q2.hfix135_29_2 Q2.hinj135_29_2
      Q2.hcardT135_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_29_2 i) (Q2.hfix135_29_2 i) _)
      colCert_135_29_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T135_29
      hfix135_29 hinj135_29 hcardT135_29
      (fun i => conj_mem_of_fixedPoints _ _ (T135_29 i) (hfix135_29 i) _)
      ⟨135, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T135_29_2 Q2.hfix135_29_2 Q2.hinj135_29_2
      Q2.hcardT135_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_29_2 i) (Q2.hfix135_29_2 i) _)
      colCert_135_29_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T135_29
      hfix135_29 hinj135_29 hcardT135_29
      (fun i => conj_mem_of_fixedPoints _ _ (T135_29 i) (hfix135_29 i) _)
      ⟨135, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T135_29_2 Q2.hfix135_29_2 Q2.hinj135_29_2
      Q2.hcardT135_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_29_2 i) (Q2.hfix135_29_2 i) _)
      colCert_135_29_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T135_29
      hfix135_29 hinj135_29 hcardT135_29
      (fun i => conj_mem_of_fixedPoints _ _ (T135_29 i) (hfix135_29 i) _)
      ⟨135, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T135_29_2 Q2.hfix135_29_2 Q2.hinj135_29_2
      Q2.hcardT135_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_29_2 i) (Q2.hfix135_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T135_29 = colFn colCertDiv_135_29_5.D1 (m := 5) from colCertDiv_135_29_5.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 5 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T135_29_2 = colFn colCertDiv_135_29_5.D2 (m := 5) from colCertDiv_135_29_5.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_29_5_match


theorem leaf_135_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T135_29
      hfix135_29 hinj135_29 hcardT135_29
      (fun i => conj_mem_of_fixedPoints _ _ (T135_29 i) (hfix135_29 i) _)
      ⟨135, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T135_29_2 Q2.hfix135_29_2 Q2.hinj135_29_2
      Q2.hcardT135_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_29_2 i) (Q2.hfix135_29_2 i) _)
      colCert_135_29_10.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T135_29
      hfix135_29 hinj135_29 hcardT135_29
      (fun i => conj_mem_of_fixedPoints _ _ (T135_29 i) (hfix135_29 i) _)
      ⟨135, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T135_29_2 Q2.hfix135_29_2 Q2.hinj135_29_2
      Q2.hcardT135_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_29_2 i) (Q2.hfix135_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T135_29 = colFn colCertDiv_135_29_15.D1 (m := 5) from colCertDiv_135_29_15.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 15 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T135_29_2 = colFn colCertDiv_135_29_15.D2 (m := 5) from colCertDiv_135_29_15.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_29_15_match


theorem leaf_135_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T135_29
      hfix135_29 hinj135_29 hcardT135_29
      (fun i => conj_mem_of_fixedPoints _ _ (T135_29 i) (hfix135_29 i) _)
      ⟨135, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T135_29_2 Q2.hfix135_29_2 Q2.hinj135_29_2
      Q2.hcardT135_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_29_2 i) (Q2.hfix135_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T135_29 = colFn colCertDiv_135_29_20.D1 (m := 5) from colCertDiv_135_29_20.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 20 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T135_29_2 = colFn colCertDiv_135_29_20.D2 (m := 5) from colCertDiv_135_29_20.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_29_20_match


theorem leaf_135_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T135_33
      hfix135_33 hinj135_33 hcardT135_33
      (fun i => conj_mem_of_fixedPoints _ _ (T135_33 i) (hfix135_33 i) _)
      ⟨135, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T135_33_2 Q2.hfix135_33_2 Q2.hinj135_33_2
      Q2.hcardT135_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_33_2 i) (Q2.hfix135_33_2 i) _)
      colCert_135_33_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T135_33
      hfix135_33 hinj135_33 hcardT135_33
      (fun i => conj_mem_of_fixedPoints _ _ (T135_33 i) (hfix135_33 i) _)
      ⟨135, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T135_33_2 Q2.hfix135_33_2 Q2.hinj135_33_2
      Q2.hcardT135_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_33_2 i) (Q2.hfix135_33_2 i) _)
      colCert_135_33_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T135_33
      hfix135_33 hinj135_33 hcardT135_33
      (fun i => conj_mem_of_fixedPoints _ _ (T135_33 i) (hfix135_33 i) _)
      ⟨135, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T135_33_2 Q2.hfix135_33_2 Q2.hinj135_33_2
      Q2.hcardT135_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_33_2 i) (Q2.hfix135_33_2 i) _)
      colCert_135_33_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T135_33
      hfix135_33 hinj135_33 hcardT135_33
      (fun i => conj_mem_of_fixedPoints _ _ (T135_33 i) (hfix135_33 i) _)
      ⟨135, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T135_33_2 Q2.hfix135_33_2 Q2.hinj135_33_2
      Q2.hcardT135_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_33_2 i) (Q2.hfix135_33_2 i) _)
      colCert_135_33_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T135_33
      hfix135_33 hinj135_33 hcardT135_33
      (fun i => conj_mem_of_fixedPoints _ _ (T135_33 i) (hfix135_33 i) _)
      ⟨135, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T135_33_2 Q2.hfix135_33_2 Q2.hinj135_33_2
      Q2.hcardT135_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_33_2 i) (Q2.hfix135_33_2 i) _)
      colCert_135_33_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T135_33
      hfix135_33 hinj135_33 hcardT135_33
      (fun i => conj_mem_of_fixedPoints _ _ (T135_33 i) (hfix135_33 i) _)
      ⟨135, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T135_33_2 Q2.hfix135_33_2 Q2.hinj135_33_2
      Q2.hcardT135_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_33_2 i) (Q2.hfix135_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T135_33 = colFn colCertDiv_135_33_5.D1 (m := 5) from colCertDiv_135_33_5.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T135_33_2 = colFn colCertDiv_135_33_5.D2 (m := 5) from colCertDiv_135_33_5.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_33_5_match


theorem leaf_135_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T135_33
      hfix135_33 hinj135_33 hcardT135_33
      (fun i => conj_mem_of_fixedPoints _ _ (T135_33 i) (hfix135_33 i) _)
      ⟨135, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T135_33_2 Q2.hfix135_33_2 Q2.hinj135_33_2
      Q2.hcardT135_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_33_2 i) (Q2.hfix135_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T135_33 = colFn colCertDiv_135_33_10.D1 (m := 5) from colCertDiv_135_33_10.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T135_33_2 = colFn colCertDiv_135_33_10.D2 (m := 5) from colCertDiv_135_33_10.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_33_10_match


theorem leaf_135_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T135_33
      hfix135_33 hinj135_33 hcardT135_33
      (fun i => conj_mem_of_fixedPoints _ _ (T135_33 i) (hfix135_33 i) _)
      ⟨135, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T135_33_2 Q2.hfix135_33_2 Q2.hinj135_33_2
      Q2.hcardT135_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_33_2 i) (Q2.hfix135_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T135_33 = colFn colCertDiv_135_33_15.D1 (m := 5) from colCertDiv_135_33_15.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T135_33_2 = colFn colCertDiv_135_33_15.D2 (m := 5) from colCertDiv_135_33_15.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_33_15_match


theorem leaf_135_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T135_33
      hfix135_33 hinj135_33 hcardT135_33
      (fun i => conj_mem_of_fixedPoints _ _ (T135_33 i) (hfix135_33 i) _)
      ⟨135, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T135_33_2 Q2.hfix135_33_2 Q2.hinj135_33_2
      Q2.hcardT135_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_33_2 i) (Q2.hfix135_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T135_33 = colFn colCertDiv_135_33_20.D1 (m := 5) from colCertDiv_135_33_20.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T135_33_2 = colFn colCertDiv_135_33_20.D2 (m := 5) from colCertDiv_135_33_20.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_33_20_match


theorem leaf_135_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T135_41
      hfix135_41 hinj135_41 hcardT135_41
      (fun i => conj_mem_of_fixedPoints _ _ (T135_41 i) (hfix135_41 i) _)
      ⟨135, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T135_41_2 Q2.hfix135_41_2 Q2.hinj135_41_2
      Q2.hcardT135_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_41_2 i) (Q2.hfix135_41_2 i) _)
      colCert_135_41_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T135_41
      hfix135_41 hinj135_41 hcardT135_41
      (fun i => conj_mem_of_fixedPoints _ _ (T135_41 i) (hfix135_41 i) _)
      ⟨135, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T135_41_2 Q2.hfix135_41_2 Q2.hinj135_41_2
      Q2.hcardT135_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_41_2 i) (Q2.hfix135_41_2 i) _)
      colCert_135_41_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T135_41
      hfix135_41 hinj135_41 hcardT135_41
      (fun i => conj_mem_of_fixedPoints _ _ (T135_41 i) (hfix135_41 i) _)
      ⟨135, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T135_41_2 Q2.hfix135_41_2 Q2.hinj135_41_2
      Q2.hcardT135_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_41_2 i) (Q2.hfix135_41_2 i) _)
      colCert_135_41_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T135_41
      hfix135_41 hinj135_41 hcardT135_41
      (fun i => conj_mem_of_fixedPoints _ _ (T135_41 i) (hfix135_41 i) _)
      ⟨135, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T135_41_2 Q2.hfix135_41_2 Q2.hinj135_41_2
      Q2.hcardT135_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_41_2 i) (Q2.hfix135_41_2 i) _)
      colCert_135_41_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T135_41
      hfix135_41 hinj135_41 hcardT135_41
      (fun i => conj_mem_of_fixedPoints _ _ (T135_41 i) (hfix135_41 i) _)
      ⟨135, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T135_41_2 Q2.hfix135_41_2 Q2.hinj135_41_2
      Q2.hcardT135_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_41_2 i) (Q2.hfix135_41_2 i) _)
      colCert_135_41_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T135_41
      hfix135_41 hinj135_41 hcardT135_41
      (fun i => conj_mem_of_fixedPoints _ _ (T135_41 i) (hfix135_41 i) _)
      ⟨135, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T135_41_2 Q2.hfix135_41_2 Q2.hinj135_41_2
      Q2.hcardT135_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_41_2 i) (Q2.hfix135_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T135_41 = colFn colCertDiv_135_41_5.D1 (m := 5) from colCertDiv_135_41_5.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T135_41_2 = colFn colCertDiv_135_41_5.D2 (m := 5) from colCertDiv_135_41_5.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_41_5_match


theorem leaf_135_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T135_41
      hfix135_41 hinj135_41 hcardT135_41
      (fun i => conj_mem_of_fixedPoints _ _ (T135_41 i) (hfix135_41 i) _)
      ⟨135, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T135_41_2 Q2.hfix135_41_2 Q2.hinj135_41_2
      Q2.hcardT135_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_41_2 i) (Q2.hfix135_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T135_41 = colFn colCertDiv_135_41_10.D1 (m := 5) from colCertDiv_135_41_10.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T135_41_2 = colFn colCertDiv_135_41_10.D2 (m := 5) from colCertDiv_135_41_10.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_41_10_match


theorem leaf_135_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T135_41
      hfix135_41 hinj135_41 hcardT135_41
      (fun i => conj_mem_of_fixedPoints _ _ (T135_41 i) (hfix135_41 i) _)
      ⟨135, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T135_41_2 Q2.hfix135_41_2 Q2.hinj135_41_2
      Q2.hcardT135_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_41_2 i) (Q2.hfix135_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T135_41 = colFn colCertDiv_135_41_15.D1 (m := 5) from colCertDiv_135_41_15.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 15 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T135_41_2 = colFn colCertDiv_135_41_15.D2 (m := 5) from colCertDiv_135_41_15.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_41_15_match


theorem leaf_135_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T135_41
      hfix135_41 hinj135_41 hcardT135_41
      (fun i => conj_mem_of_fixedPoints _ _ (T135_41 i) (hfix135_41 i) _)
      ⟨135, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T135_41_2 Q2.hfix135_41_2 Q2.hinj135_41_2
      Q2.hcardT135_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_41_2 i) (Q2.hfix135_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T135_41 = colFn colCertDiv_135_41_20.D1 (m := 5) from colCertDiv_135_41_20.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T135_41_2 = colFn colCertDiv_135_41_20.D2 (m := 5) from colCertDiv_135_41_20.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_41_20_match


theorem leaf_135_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T135_45
      hfix135_45 hinj135_45 hcardT135_45
      (fun i => conj_mem_of_fixedPoints _ _ (T135_45 i) (hfix135_45 i) _)
      ⟨135, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T135_45_2 Q2.hfix135_45_2 Q2.hinj135_45_2
      Q2.hcardT135_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_45_2 i) (Q2.hfix135_45_2 i) _)
      colCert_135_45_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T135_45
      hfix135_45 hinj135_45 hcardT135_45
      (fun i => conj_mem_of_fixedPoints _ _ (T135_45 i) (hfix135_45 i) _)
      ⟨135, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T135_45_2 Q2.hfix135_45_2 Q2.hinj135_45_2
      Q2.hcardT135_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_45_2 i) (Q2.hfix135_45_2 i) _)
      colCert_135_45_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T135_45
      hfix135_45 hinj135_45 hcardT135_45
      (fun i => conj_mem_of_fixedPoints _ _ (T135_45 i) (hfix135_45 i) _)
      ⟨135, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T135_45_2 Q2.hfix135_45_2 Q2.hinj135_45_2
      Q2.hcardT135_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_45_2 i) (Q2.hfix135_45_2 i) _)
      colCert_135_45_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T135_45
      hfix135_45 hinj135_45 hcardT135_45
      (fun i => conj_mem_of_fixedPoints _ _ (T135_45 i) (hfix135_45 i) _)
      ⟨135, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T135_45_2 Q2.hfix135_45_2 Q2.hinj135_45_2
      Q2.hcardT135_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_45_2 i) (Q2.hfix135_45_2 i) _)
      colCert_135_45_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T135_45
      hfix135_45 hinj135_45 hcardT135_45
      (fun i => conj_mem_of_fixedPoints _ _ (T135_45 i) (hfix135_45 i) _)
      ⟨135, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T135_45_2 Q2.hfix135_45_2 Q2.hinj135_45_2
      Q2.hcardT135_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_45_2 i) (Q2.hfix135_45_2 i) _)
      colCert_135_45_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T135_45
      hfix135_45 hinj135_45 hcardT135_45
      (fun i => conj_mem_of_fixedPoints _ _ (T135_45 i) (hfix135_45 i) _)
      ⟨135, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T135_45_2 Q2.hfix135_45_2 Q2.hinj135_45_2
      Q2.hcardT135_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_45_2 i) (Q2.hfix135_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T135_45 = colFn colCertDiv_135_45_5.D1 (m := 5) from colCertDiv_135_45_5.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T135_45_2 = colFn colCertDiv_135_45_5.D2 (m := 5) from colCertDiv_135_45_5.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_45_5_match


theorem leaf_135_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T135_45
      hfix135_45 hinj135_45 hcardT135_45
      (fun i => conj_mem_of_fixedPoints _ _ (T135_45 i) (hfix135_45 i) _)
      ⟨135, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T135_45_2 Q2.hfix135_45_2 Q2.hinj135_45_2
      Q2.hcardT135_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_45_2 i) (Q2.hfix135_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T135_45 = colFn colCertDiv_135_45_10.D1 (m := 5) from colCertDiv_135_45_10.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T135_45_2 = colFn colCertDiv_135_45_10.D2 (m := 5) from colCertDiv_135_45_10.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_45_10_match


theorem leaf_135_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T135_45
      hfix135_45 hinj135_45 hcardT135_45
      (fun i => conj_mem_of_fixedPoints _ _ (T135_45 i) (hfix135_45 i) _)
      ⟨135, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T135_45_2 Q2.hfix135_45_2 Q2.hinj135_45_2
      Q2.hcardT135_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_45_2 i) (Q2.hfix135_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T135_45 = colFn colCertDiv_135_45_15.D1 (m := 5) from colCertDiv_135_45_15.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 15 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T135_45_2 = colFn colCertDiv_135_45_15.D2 (m := 5) from colCertDiv_135_45_15.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_45_15_match


theorem leaf_135_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T135_45
      hfix135_45 hinj135_45 hcardT135_45
      (fun i => conj_mem_of_fixedPoints _ _ (T135_45 i) (hfix135_45 i) _)
      ⟨135, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T135_45_2 Q2.hfix135_45_2 Q2.hinj135_45_2
      Q2.hcardT135_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_45_2 i) (Q2.hfix135_45_2 i) _)
      colCert_135_45_20.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_52_0 (hp : 0 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 0 (transLenTr ⟨52, by decide⟩ 0 hp)) T135_52
      hfix135_52 hinj135_52 hcardT135_52
      (fun i => conj_mem_of_fixedPoints _ _ (T135_52 i) (hfix135_52 i) _)
      ⟨135, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 0 hp) Q2.T135_52_2 Q2.hfix135_52_2 Q2.hinj135_52_2
      Q2.hcardT135_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_52_2 i) (Q2.hfix135_52_2 i) _)
      colCert_135_52_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_52_1 (hp : 1 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 1 (transLenTr ⟨52, by decide⟩ 1 hp)) T135_52
      hfix135_52 hinj135_52 hcardT135_52
      (fun i => conj_mem_of_fixedPoints _ _ (T135_52 i) (hfix135_52 i) _)
      ⟨135, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 1 hp) Q2.T135_52_2 Q2.hfix135_52_2 Q2.hinj135_52_2
      Q2.hcardT135_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_52_2 i) (Q2.hfix135_52_2 i) _)
      colCert_135_52_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_52_2 (hp : 2 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 2 (transLenTr ⟨52, by decide⟩ 2 hp)) T135_52
      hfix135_52 hinj135_52 hcardT135_52
      (fun i => conj_mem_of_fixedPoints _ _ (T135_52 i) (hfix135_52 i) _)
      ⟨135, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 2 hp) Q2.T135_52_2 Q2.hfix135_52_2 Q2.hinj135_52_2
      Q2.hcardT135_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_52_2 i) (Q2.hfix135_52_2 i) _)
      colCert_135_52_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_52_3 (hp : 3 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 3 (transLenTr ⟨52, by decide⟩ 3 hp)) T135_52
      hfix135_52 hinj135_52 hcardT135_52
      (fun i => conj_mem_of_fixedPoints _ _ (T135_52 i) (hfix135_52 i) _)
      ⟨135, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 3 hp) Q2.T135_52_2 Q2.hfix135_52_2 Q2.hinj135_52_2
      Q2.hcardT135_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_52_2 i) (Q2.hfix135_52_2 i) _)
      colCert_135_52_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_52_4 (hp : 4 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 4 (transLenTr ⟨52, by decide⟩ 4 hp)) T135_52
      hfix135_52 hinj135_52 hcardT135_52
      (fun i => conj_mem_of_fixedPoints _ _ (T135_52 i) (hfix135_52 i) _)
      ⟨135, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 4 hp) Q2.T135_52_2 Q2.hfix135_52_2 Q2.hinj135_52_2
      Q2.hcardT135_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_52_2 i) (Q2.hfix135_52_2 i) _)
      colCert_135_52_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_52_5 (hp : 5 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp)) T135_52
      hfix135_52 hinj135_52 hcardT135_52
      (fun i => conj_mem_of_fixedPoints _ _ (T135_52 i) (hfix135_52 i) _)
      ⟨135, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 5 hp) Q2.T135_52_2 Q2.hfix135_52_2 Q2.hinj135_52_2
      Q2.hcardT135_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_52_2 i) (Q2.hfix135_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 5 (transLenTr ⟨52, by decide⟩ 5 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T135_52 = colFn colCertDiv_135_52_5.D1 (m := 5) from colCertDiv_135_52_5.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 5 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T135_52_2 = colFn colCertDiv_135_52_5.D2 (m := 5) from colCertDiv_135_52_5.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_52_5_match


theorem leaf_135_52_10 (hp : 10 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp)) T135_52
      hfix135_52 hinj135_52 hcardT135_52
      (fun i => conj_mem_of_fixedPoints _ _ (T135_52 i) (hfix135_52 i) _)
      ⟨135, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 10 hp) Q2.T135_52_2 Q2.hfix135_52_2 Q2.hinj135_52_2
      Q2.hcardT135_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_52_2 i) (Q2.hfix135_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 10 (transLenTr ⟨52, by decide⟩ 10 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T135_52 = colFn colCertDiv_135_52_10.D1 (m := 5) from colCertDiv_135_52_10.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 10 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T135_52_2 = colFn colCertDiv_135_52_10.D2 (m := 5) from colCertDiv_135_52_10.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_52_10_match


theorem leaf_135_52_15 (hp : 15 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp)) T135_52
      hfix135_52 hinj135_52 hcardT135_52
      (fun i => conj_mem_of_fixedPoints _ _ (T135_52 i) (hfix135_52 i) _)
      ⟨135, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 15 hp) Q2.T135_52_2 Q2.hfix135_52_2 Q2.hinj135_52_2
      Q2.hcardT135_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_52_2 i) (Q2.hfix135_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 15 (transLenTr ⟨52, by decide⟩ 15 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T135_52 = colFn colCertDiv_135_52_15.D1 (m := 5) from colCertDiv_135_52_15.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 15 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T135_52_2 = colFn colCertDiv_135_52_15.D2 (m := 5) from colCertDiv_135_52_15.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_52_15_match


theorem leaf_135_52_20 (hp : 20 < (Q2.transData.getD 52 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨52, by decide⟩ : Fin 148)) (colE2 ⟨52, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨52, by decide⟩ : Fin 148))
        (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨52, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp)) T135_52
      hfix135_52 hinj135_52 hcardT135_52
      (fun i => conj_mem_of_fixedPoints _ _ (T135_52 i) (hfix135_52 i) _)
      ⟨135, by decide⟩ ⟨52, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨52, by decide⟩ 20 hp) Q2.T135_52_2 Q2.hfix135_52_2 Q2.hinj135_52_2
      Q2.hcardT135_52_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_52_2 i) (Q2.hfix135_52_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨52, by decide⟩ 20 (transLenTr ⟨52, by decide⟩ 20 hp) : ↥(reps ⟨52, by decide⟩)) : Coordinate 1)
        T135_52 = colFn colCertDiv_135_52_20.D1 (m := 5) from colCertDiv_135_52_20.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨52, by decide⟩ 20 hp : ↥(Q2.reps ⟨52, by decide⟩)) : Coordinate 2)
        Q2.T135_52_2 = colFn colCertDiv_135_52_20.D2 (m := 5) from colCertDiv_135_52_20.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_52_20_match


theorem leaf_135_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T135_53
      hfix135_53 hinj135_53 hcardT135_53
      (fun i => conj_mem_of_fixedPoints _ _ (T135_53 i) (hfix135_53 i) _)
      ⟨135, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T135_53_2 Q2.hfix135_53_2 Q2.hinj135_53_2
      Q2.hcardT135_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_53_2 i) (Q2.hfix135_53_2 i) _)
      colCert_135_53_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T135_53
      hfix135_53 hinj135_53 hcardT135_53
      (fun i => conj_mem_of_fixedPoints _ _ (T135_53 i) (hfix135_53 i) _)
      ⟨135, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T135_53_2 Q2.hfix135_53_2 Q2.hinj135_53_2
      Q2.hcardT135_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_53_2 i) (Q2.hfix135_53_2 i) _)
      colCert_135_53_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T135_53
      hfix135_53 hinj135_53 hcardT135_53
      (fun i => conj_mem_of_fixedPoints _ _ (T135_53 i) (hfix135_53 i) _)
      ⟨135, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T135_53_2 Q2.hfix135_53_2 Q2.hinj135_53_2
      Q2.hcardT135_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_53_2 i) (Q2.hfix135_53_2 i) _)
      colCert_135_53_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T135_53
      hfix135_53 hinj135_53 hcardT135_53
      (fun i => conj_mem_of_fixedPoints _ _ (T135_53 i) (hfix135_53 i) _)
      ⟨135, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T135_53_2 Q2.hfix135_53_2 Q2.hinj135_53_2
      Q2.hcardT135_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_53_2 i) (Q2.hfix135_53_2 i) _)
      colCert_135_53_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T135_53
      hfix135_53 hinj135_53 hcardT135_53
      (fun i => conj_mem_of_fixedPoints _ _ (T135_53 i) (hfix135_53 i) _)
      ⟨135, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T135_53_2 Q2.hfix135_53_2 Q2.hinj135_53_2
      Q2.hcardT135_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_53_2 i) (Q2.hfix135_53_2 i) _)
      colCert_135_53_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T135_53
      hfix135_53 hinj135_53 hcardT135_53
      (fun i => conj_mem_of_fixedPoints _ _ (T135_53 i) (hfix135_53 i) _)
      ⟨135, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T135_53_2 Q2.hfix135_53_2 Q2.hinj135_53_2
      Q2.hcardT135_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_53_2 i) (Q2.hfix135_53_2 i) _)
      colCert_135_53_5.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T135_53
      hfix135_53 hinj135_53 hcardT135_53
      (fun i => conj_mem_of_fixedPoints _ _ (T135_53 i) (hfix135_53 i) _)
      ⟨135, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T135_53_2 Q2.hfix135_53_2 Q2.hinj135_53_2
      Q2.hcardT135_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_53_2 i) (Q2.hfix135_53_2 i) _)
      colCert_135_53_10.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T135_53
      hfix135_53 hinj135_53 hcardT135_53
      (fun i => conj_mem_of_fixedPoints _ _ (T135_53 i) (hfix135_53 i) _)
      ⟨135, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T135_53_2 Q2.hfix135_53_2 Q2.hinj135_53_2
      Q2.hcardT135_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_53_2 i) (Q2.hfix135_53_2 i) _)
      colCert_135_53_15.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T135_53
      hfix135_53 hinj135_53 hcardT135_53
      (fun i => conj_mem_of_fixedPoints _ _ (T135_53 i) (hfix135_53 i) _)
      ⟨135, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T135_53_2 Q2.hfix135_53_2 Q2.hinj135_53_2
      Q2.hcardT135_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_53_2 i) (Q2.hfix135_53_2 i) _)
      colCert_135_53_20.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_83_0 (hp : 0 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp)) T135_83
      hfix135_83 hinj135_83 hcardT135_83
      (fun i => conj_mem_of_fixedPoints _ _ (T135_83 i) (hfix135_83 i) _)
      ⟨135, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 0 hp) Q2.T135_83_2 Q2.hfix135_83_2 Q2.hinj135_83_2
      Q2.hcardT135_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_83_2 i) (Q2.hfix135_83_2 i) _)
      colCert_135_83_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_83_1 (hp : 1 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp)) T135_83
      hfix135_83 hinj135_83 hcardT135_83
      (fun i => conj_mem_of_fixedPoints _ _ (T135_83 i) (hfix135_83 i) _)
      ⟨135, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 1 hp) Q2.T135_83_2 Q2.hfix135_83_2 Q2.hinj135_83_2
      Q2.hcardT135_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_83_2 i) (Q2.hfix135_83_2 i) _)
      colCert_135_83_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_83_2 (hp : 2 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp)) T135_83
      hfix135_83 hinj135_83 hcardT135_83
      (fun i => conj_mem_of_fixedPoints _ _ (T135_83 i) (hfix135_83 i) _)
      ⟨135, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 2 hp) Q2.T135_83_2 Q2.hfix135_83_2 Q2.hinj135_83_2
      Q2.hcardT135_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_83_2 i) (Q2.hfix135_83_2 i) _)
      colCert_135_83_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_83_3 (hp : 3 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp)) T135_83
      hfix135_83 hinj135_83 hcardT135_83
      (fun i => conj_mem_of_fixedPoints _ _ (T135_83 i) (hfix135_83 i) _)
      ⟨135, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 3 hp) Q2.T135_83_2 Q2.hfix135_83_2 Q2.hinj135_83_2
      Q2.hcardT135_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_83_2 i) (Q2.hfix135_83_2 i) _)
      colCert_135_83_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_83_4 (hp : 4 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp)) T135_83
      hfix135_83 hinj135_83 hcardT135_83
      (fun i => conj_mem_of_fixedPoints _ _ (T135_83 i) (hfix135_83 i) _)
      ⟨135, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 4 hp) Q2.T135_83_2 Q2.hfix135_83_2 Q2.hinj135_83_2
      Q2.hcardT135_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_83_2 i) (Q2.hfix135_83_2 i) _)
      colCert_135_83_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_83_5 (hp : 5 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp)) T135_83
      hfix135_83 hinj135_83 hcardT135_83
      (fun i => conj_mem_of_fixedPoints _ _ (T135_83 i) (hfix135_83 i) _)
      ⟨135, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 5 hp) Q2.T135_83_2 Q2.hfix135_83_2 Q2.hinj135_83_2
      Q2.hcardT135_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_83_2 i) (Q2.hfix135_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T135_83 = colFn colCertDiv_135_83_5.D1 (m := 5) from colCertDiv_135_83_5.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 5 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T135_83_2 = colFn colCertDiv_135_83_5.D2 (m := 5) from colCertDiv_135_83_5.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_83_5_match


theorem leaf_135_83_10 (hp : 10 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp)) T135_83
      hfix135_83 hinj135_83 hcardT135_83
      (fun i => conj_mem_of_fixedPoints _ _ (T135_83 i) (hfix135_83 i) _)
      ⟨135, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 10 hp) Q2.T135_83_2 Q2.hfix135_83_2 Q2.hinj135_83_2
      Q2.hcardT135_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_83_2 i) (Q2.hfix135_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T135_83 = colFn colCertDiv_135_83_10.D1 (m := 5) from colCertDiv_135_83_10.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 10 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T135_83_2 = colFn colCertDiv_135_83_10.D2 (m := 5) from colCertDiv_135_83_10.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_83_10_match


theorem leaf_135_83_15 (hp : 15 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp)) T135_83
      hfix135_83 hinj135_83 hcardT135_83
      (fun i => conj_mem_of_fixedPoints _ _ (T135_83 i) (hfix135_83 i) _)
      ⟨135, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 15 hp) Q2.T135_83_2 Q2.hfix135_83_2 Q2.hinj135_83_2
      Q2.hcardT135_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_83_2 i) (Q2.hfix135_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T135_83 = colFn colCertDiv_135_83_15.D1 (m := 5) from colCertDiv_135_83_15.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 15 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T135_83_2 = colFn colCertDiv_135_83_15.D2 (m := 5) from colCertDiv_135_83_15.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_83_15_match


theorem leaf_135_83_20 (hp : 20 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp)) T135_83
      hfix135_83 hinj135_83 hcardT135_83
      (fun i => conj_mem_of_fixedPoints _ _ (T135_83 i) (hfix135_83 i) _)
      ⟨135, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 20 hp) Q2.T135_83_2 Q2.hfix135_83_2 Q2.hinj135_83_2
      Q2.hcardT135_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_83_2 i) (Q2.hfix135_83_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp) : ↥(reps ⟨83, by decide⟩)) : Coordinate 1)
        T135_83 = colFn colCertDiv_135_83_20.D1 (m := 5) from colCertDiv_135_83_20.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨83, by decide⟩ 20 hp : ↥(Q2.reps ⟨83, by decide⟩)) : Coordinate 2)
        Q2.T135_83_2 = colFn colCertDiv_135_83_20.D2 (m := 5) from colCertDiv_135_83_20.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_83_20_match


theorem leaf_135_91_0 (hp : 0 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp)) T135_91
      hfix135_91 hinj135_91 hcardT135_91
      (fun i => conj_mem_of_fixedPoints _ _ (T135_91 i) (hfix135_91 i) _)
      ⟨135, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 0 hp) Q2.T135_91_2 Q2.hfix135_91_2 Q2.hinj135_91_2
      Q2.hcardT135_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_91_2 i) (Q2.hfix135_91_2 i) _)
      colCert_135_91_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_91_1 (hp : 1 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp)) T135_91
      hfix135_91 hinj135_91 hcardT135_91
      (fun i => conj_mem_of_fixedPoints _ _ (T135_91 i) (hfix135_91 i) _)
      ⟨135, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 1 hp) Q2.T135_91_2 Q2.hfix135_91_2 Q2.hinj135_91_2
      Q2.hcardT135_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_91_2 i) (Q2.hfix135_91_2 i) _)
      colCert_135_91_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_91_2 (hp : 2 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp)) T135_91
      hfix135_91 hinj135_91 hcardT135_91
      (fun i => conj_mem_of_fixedPoints _ _ (T135_91 i) (hfix135_91 i) _)
      ⟨135, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 2 hp) Q2.T135_91_2 Q2.hfix135_91_2 Q2.hinj135_91_2
      Q2.hcardT135_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_91_2 i) (Q2.hfix135_91_2 i) _)
      colCert_135_91_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_91_3 (hp : 3 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp)) T135_91
      hfix135_91 hinj135_91 hcardT135_91
      (fun i => conj_mem_of_fixedPoints _ _ (T135_91 i) (hfix135_91 i) _)
      ⟨135, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 3 hp) Q2.T135_91_2 Q2.hfix135_91_2 Q2.hinj135_91_2
      Q2.hcardT135_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_91_2 i) (Q2.hfix135_91_2 i) _)
      colCert_135_91_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_91_4 (hp : 4 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp)) T135_91
      hfix135_91 hinj135_91 hcardT135_91
      (fun i => conj_mem_of_fixedPoints _ _ (T135_91 i) (hfix135_91 i) _)
      ⟨135, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 4 hp) Q2.T135_91_2 Q2.hfix135_91_2 Q2.hinj135_91_2
      Q2.hcardT135_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_91_2 i) (Q2.hfix135_91_2 i) _)
      colCert_135_91_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_91_5 (hp : 5 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp)) T135_91
      hfix135_91 hinj135_91 hcardT135_91
      (fun i => conj_mem_of_fixedPoints _ _ (T135_91 i) (hfix135_91 i) _)
      ⟨135, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 5 hp) Q2.T135_91_2 Q2.hfix135_91_2 Q2.hinj135_91_2
      Q2.hcardT135_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_91_2 i) (Q2.hfix135_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T135_91 = colFn colCertDiv_135_91_5.D1 (m := 5) from colCertDiv_135_91_5.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 5 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T135_91_2 = colFn colCertDiv_135_91_5.D2 (m := 5) from colCertDiv_135_91_5.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_91_5_match


theorem leaf_135_91_10 (hp : 10 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp)) T135_91
      hfix135_91 hinj135_91 hcardT135_91
      (fun i => conj_mem_of_fixedPoints _ _ (T135_91 i) (hfix135_91 i) _)
      ⟨135, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 10 hp) Q2.T135_91_2 Q2.hfix135_91_2 Q2.hinj135_91_2
      Q2.hcardT135_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_91_2 i) (Q2.hfix135_91_2 i) _)
      colCert_135_91_10.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_91_15 (hp : 15 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp)) T135_91
      hfix135_91 hinj135_91 hcardT135_91
      (fun i => conj_mem_of_fixedPoints _ _ (T135_91 i) (hfix135_91 i) _)
      ⟨135, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 15 hp) Q2.T135_91_2 Q2.hfix135_91_2 Q2.hinj135_91_2
      Q2.hcardT135_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_91_2 i) (Q2.hfix135_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T135_91 = colFn colCertDiv_135_91_15.D1 (m := 5) from colCertDiv_135_91_15.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 15 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T135_91_2 = colFn colCertDiv_135_91_15.D2 (m := 5) from colCertDiv_135_91_15.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_91_15_match


theorem leaf_135_91_20 (hp : 20 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp)) T135_91
      hfix135_91 hinj135_91 hcardT135_91
      (fun i => conj_mem_of_fixedPoints _ _ (T135_91 i) (hfix135_91 i) _)
      ⟨135, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 20 hp) Q2.T135_91_2 Q2.hfix135_91_2 Q2.hinj135_91_2
      Q2.hcardT135_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_91_2 i) (Q2.hfix135_91_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp) : ↥(reps ⟨91, by decide⟩)) : Coordinate 1)
        T135_91 = colFn colCertDiv_135_91_20.D1 (m := 5) from colCertDiv_135_91_20.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨91, by decide⟩ 20 hp : ↥(Q2.reps ⟨91, by decide⟩)) : Coordinate 2)
        Q2.T135_91_2 = colFn colCertDiv_135_91_20.D2 (m := 5) from colCertDiv_135_91_20.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_91_20_match


theorem leaf_135_95_0 (hp : 0 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 0 (transLenTr ⟨95, by decide⟩ 0 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 0 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      colCert_135_95_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_95_1 (hp : 1 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 1 (transLenTr ⟨95, by decide⟩ 1 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 1 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      colCert_135_95_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_95_2 (hp : 2 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 2 (transLenTr ⟨95, by decide⟩ 2 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 2 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      colCert_135_95_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_95_3 (hp : 3 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 3 (transLenTr ⟨95, by decide⟩ 3 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 3 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      colCert_135_95_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_95_4 (hp : 4 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 4 (transLenTr ⟨95, by decide⟩ 4 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 4 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      colCert_135_95_4.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_95_5 (hp : 5 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 5 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 5 (transLenTr ⟨95, by decide⟩ 5 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 5 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      colCert_135_95_5.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_95_10 (hp : 10 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 10 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 10 (transLenTr ⟨95, by decide⟩ 10 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 10 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      colCert_135_95_10.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_95_15 (hp : 15 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 15 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 15 (transLenTr ⟨95, by decide⟩ 15 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 15 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      colCert_135_95_15.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_95_20 (hp : 20 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 20 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 20 (transLenTr ⟨95, by decide⟩ 20 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 20 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      colCert_135_95_20.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_95_25 (hp : 25 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 25 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 25 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 25 (transLenTr ⟨95, by decide⟩ 25 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T135_95 = colFn colCertDiv_135_95_25.D1 (m := 5) from colCertDiv_135_95_25.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 25 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T135_95_2 = colFn colCertDiv_135_95_25.D2 (m := 5) from colCertDiv_135_95_25.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_95_25_match


theorem leaf_135_95_50 (hp : 50 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 50 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 50 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 50 (transLenTr ⟨95, by decide⟩ 50 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T135_95 = colFn colCertDiv_135_95_50.D1 (m := 5) from colCertDiv_135_95_50.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 50 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T135_95_2 = colFn colCertDiv_135_95_50.D2 (m := 5) from colCertDiv_135_95_50.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_95_50_match


theorem leaf_135_95_75 (hp : 75 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 75 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 75 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 75 (transLenTr ⟨95, by decide⟩ 75 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T135_95 = colFn colCertDiv_135_95_75.D1 (m := 5) from colCertDiv_135_95_75.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 75 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T135_95_2 = colFn colCertDiv_135_95_75.D2 (m := 5) from colCertDiv_135_95_75.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_95_75_match


theorem leaf_135_95_100 (hp : 100 < (Q2.transData.getD 95 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨95, by decide⟩ : Fin 148)) (colE2 ⟨95, by decide⟩ 100 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨95, by decide⟩ : Fin 148))
        (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨135, by decide⟩ : Fin 148) ⟨95, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp)) T135_95
      hfix135_95 hinj135_95 hcardT135_95
      (fun i => conj_mem_of_fixedPoints _ _ (T135_95 i) (hfix135_95 i) _)
      ⟨135, by decide⟩ ⟨95, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨95, by decide⟩ 100 hp) Q2.T135_95_2 Q2.hfix135_95_2 Q2.hinj135_95_2
      Q2.hcardT135_95_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_95_2 i) (Q2.hfix135_95_2 i) _)
      ?_).symm
  rw [show colData1 (⟨135, by decide⟩ : Fin 148)
        ((colE1 ⟨95, by decide⟩ 100 (transLenTr ⟨95, by decide⟩ 100 hp) : ↥(reps ⟨95, by decide⟩)) : Coordinate 1)
        T135_95 = colFn colCertDiv_135_95_100.D1 (m := 5) from colCertDiv_135_95_100.bind1,
    show colData2 (⟨135, by decide⟩ : Fin 148)
        ((colE2 ⟨95, by decide⟩ 100 hp : ↥(Q2.reps ⟨95, by decide⟩)) : Coordinate 2)
        Q2.T135_95_2 = colFn colCertDiv_135_95_100.D2 (m := 5) from colCertDiv_135_95_100.bind2]
  rw [alnId_135 j hj]
  exact fastcode_of_div ⟨135, by decide⟩ _ _ _
    ((alnId_135 j hj) ▸ Q2.listedAt (⟨135, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨135, by decide⟩ : Fin 148) hj hq).1) colCertDiv_135_95_100_match


theorem leaf_135_103_0 (hp : 0 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 0 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 0 (transLenTr ⟨103, by decide⟩ 0 hp)) T135_103
      hfix135_103 hinj135_103 hcardT135_103
      (fun i => conj_mem_of_fixedPoints _ _ (T135_103 i) (hfix135_103 i) _)
      ⟨135, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 0 hp) Q2.T135_103_2 Q2.hfix135_103_2 Q2.hinj135_103_2
      Q2.hcardT135_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_103_2 i) (Q2.hfix135_103_2 i) _)
      colCert_135_103_0.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_103_1 (hp : 1 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 1 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 1 (transLenTr ⟨103, by decide⟩ 1 hp)) T135_103
      hfix135_103 hinj135_103 hcardT135_103
      (fun i => conj_mem_of_fixedPoints _ _ (T135_103 i) (hfix135_103 i) _)
      ⟨135, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 1 hp) Q2.T135_103_2 Q2.hfix135_103_2 Q2.hinj135_103_2
      Q2.hcardT135_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_103_2 i) (Q2.hfix135_103_2 i) _)
      colCert_135_103_1.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_103_2 (hp : 2 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 2 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 2 (transLenTr ⟨103, by decide⟩ 2 hp)) T135_103
      hfix135_103 hinj135_103 hcardT135_103
      (fun i => conj_mem_of_fixedPoints _ _ (T135_103 i) (hfix135_103 i) _)
      ⟨135, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 2 hp) Q2.T135_103_2 Q2.hfix135_103_2 Q2.hinj135_103_2
      Q2.hcardT135_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_103_2 i) (Q2.hfix135_103_2 i) _)
      colCert_135_103_2.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_103_3 (hp : 3 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 3 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 3 (transLenTr ⟨103, by decide⟩ 3 hp)) T135_103
      hfix135_103 hinj135_103 hcardT135_103
      (fun i => conj_mem_of_fixedPoints _ _ (T135_103 i) (hfix135_103 i) _)
      ⟨135, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 3 hp) Q2.T135_103_2 Q2.hfix135_103_2 Q2.hinj135_103_2
      Q2.hcardT135_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_103_2 i) (Q2.hfix135_103_2 i) _)
      colCert_135_103_3.hD ?_).symm
  rw [alnId_135 j hj]


theorem leaf_135_103_4 (hp : 4 < (Q2.transData.getD 103 []).length)
    (j : Nat) (hj : j < (repChars.getD 135 []).length)
    (hq : (normIsRep.getD 135 []).getD j false = true) :
    species (Q2.reps (⟨103, by decide⟩ : Fin 148)) (colE2 ⟨103, by decide⟩ 4 hp)
        (rowE2 (⟨135, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨103, by decide⟩ : Fin 148))
        (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp))
        (rowE1 (⟨135, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨135, by decide⟩ : Fin 148) ⟨103, by decide⟩ _
      (validAt ⟨135, by decide⟩ (listedAt ⟨135, by decide⟩ hj))
      (colE1 ⟨103, by decide⟩ 4 (transLenTr ⟨103, by decide⟩ 4 hp)) T135_103
      hfix135_103 hinj135_103 hcardT135_103
      (fun i => conj_mem_of_fixedPoints _ _ (T135_103 i) (hfix135_103 i) _)
      ⟨135, by decide⟩ ⟨103, by decide⟩ _
      (Q2.validAt ⟨135, by decide⟩ (Q2.listedAt ⟨135, by decide⟩
        (alnCheck_rep ⟨135, by decide⟩ hj hq).1))
      (colE2 ⟨103, by decide⟩ 4 hp) Q2.T135_103_2 Q2.hfix135_103_2 Q2.hinj135_103_2
      Q2.hcardT135_103_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T135_103_2 i) (Q2.hfix135_103_2 i) _)
      colCert_135_103_4.hD ?_).symm
  rw [alnId_135 j hj]


end LeanDring.P5Presentation
