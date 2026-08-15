/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C090
import LeanDring.P5.Data.ColRestCheap.C091
import LeanDring.P5.Data.ColRestCheap.C092
import LeanDring.P5.Data.ColRestCheap.C093
import LeanDring.P5.Data.ColRestCheap.C094
import LeanDring.P5.Data.EntryK.C040
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore

/-! # Stage-5 leaves, chunk 43 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_141_16_13 (hp : 13 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 13 (transLenTr ⟨16, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 13 (transLenTr ⟨16, by decide⟩ 13 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 13 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_14 (hp : 14 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 14 (transLenTr ⟨16, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 14 (transLenTr ⟨16, by decide⟩ 14 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 14 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_15 (hp : 15 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 15 (transLenTr ⟨16, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 15 (transLenTr ⟨16, by decide⟩ 15 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 15 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_16 (hp : 16 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 16 (transLenTr ⟨16, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 16 (transLenTr ⟨16, by decide⟩ 16 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 16 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_17 (hp : 17 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 17 (transLenTr ⟨16, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 17 (transLenTr ⟨16, by decide⟩ 17 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 17 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_18 (hp : 18 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 18 (transLenTr ⟨16, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 18 (transLenTr ⟨16, by decide⟩ 18 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 18 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_19 (hp : 19 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 19 (transLenTr ⟨16, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 19 (transLenTr ⟨16, by decide⟩ 19 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 19 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_20 (hp : 20 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 20 (transLenTr ⟨16, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 20 (transLenTr ⟨16, by decide⟩ 20 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 20 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_21 (hp : 21 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 21 (transLenTr ⟨16, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 21 (transLenTr ⟨16, by decide⟩ 21 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 21 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_22 (hp : 22 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 22 (transLenTr ⟨16, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 22 (transLenTr ⟨16, by decide⟩ 22 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 22 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_23 (hp : 23 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 23 (transLenTr ⟨16, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 23 (transLenTr ⟨16, by decide⟩ 23 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 23 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_16_24 (hp : 24 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 24 (transLenTr ⟨16, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 24 (transLenTr ⟨16, by decide⟩ 24 hp)) T141_16
      hfix141_16 hinj141_16 hcardT141_16
      (fun i => conj_mem_of_fixedPoints _ _ (T141_16 i) (hfix141_16 i) _)
      ⟨141, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 24 hp) Q2.T141_16_2 Q2.hfix141_16_2 Q2.hinj141_16_2
      Q2.hcardT141_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_16_2 i) (Q2.hfix141_16_2 i) _)
      colCert_141_16_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_0 (hp : 0 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 0 (transLenTr ⟨17, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 0 (transLenTr ⟨17, by decide⟩ 0 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 0 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_1 (hp : 1 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 1 (transLenTr ⟨17, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 1 (transLenTr ⟨17, by decide⟩ 1 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 1 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_2 (hp : 2 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 2 (transLenTr ⟨17, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 2 (transLenTr ⟨17, by decide⟩ 2 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 2 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_3 (hp : 3 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 3 (transLenTr ⟨17, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 3 (transLenTr ⟨17, by decide⟩ 3 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 3 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_4 (hp : 4 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 4 (transLenTr ⟨17, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 4 (transLenTr ⟨17, by decide⟩ 4 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 4 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_5 (hp : 5 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 5 (transLenTr ⟨17, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 5 (transLenTr ⟨17, by decide⟩ 5 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 5 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_6 (hp : 6 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 6 (transLenTr ⟨17, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 6 (transLenTr ⟨17, by decide⟩ 6 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 6 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_7 (hp : 7 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 7 (transLenTr ⟨17, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 7 (transLenTr ⟨17, by decide⟩ 7 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 7 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_8 (hp : 8 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 8 (transLenTr ⟨17, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 8 (transLenTr ⟨17, by decide⟩ 8 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 8 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_9 (hp : 9 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 9 (transLenTr ⟨17, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 9 (transLenTr ⟨17, by decide⟩ 9 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 9 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_10 (hp : 10 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 10 (transLenTr ⟨17, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 10 (transLenTr ⟨17, by decide⟩ 10 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 10 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_11 (hp : 11 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 11 (transLenTr ⟨17, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 11 (transLenTr ⟨17, by decide⟩ 11 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 11 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_12 (hp : 12 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 12 (transLenTr ⟨17, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 12 (transLenTr ⟨17, by decide⟩ 12 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 12 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_13 (hp : 13 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 13 (transLenTr ⟨17, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 13 (transLenTr ⟨17, by decide⟩ 13 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 13 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_14 (hp : 14 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 14 (transLenTr ⟨17, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 14 (transLenTr ⟨17, by decide⟩ 14 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 14 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_15 (hp : 15 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 15 (transLenTr ⟨17, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 15 (transLenTr ⟨17, by decide⟩ 15 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 15 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_16 (hp : 16 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 16 (transLenTr ⟨17, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 16 (transLenTr ⟨17, by decide⟩ 16 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 16 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_17 (hp : 17 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 17 (transLenTr ⟨17, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 17 (transLenTr ⟨17, by decide⟩ 17 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 17 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_18 (hp : 18 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 18 (transLenTr ⟨17, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 18 (transLenTr ⟨17, by decide⟩ 18 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 18 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_19 (hp : 19 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 19 (transLenTr ⟨17, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 19 (transLenTr ⟨17, by decide⟩ 19 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 19 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_20 (hp : 20 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 20 (transLenTr ⟨17, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 20 (transLenTr ⟨17, by decide⟩ 20 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 20 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_21 (hp : 21 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 21 (transLenTr ⟨17, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 21 (transLenTr ⟨17, by decide⟩ 21 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 21 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_22 (hp : 22 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 22 (transLenTr ⟨17, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 22 (transLenTr ⟨17, by decide⟩ 22 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 22 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_23 (hp : 23 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 23 (transLenTr ⟨17, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 23 (transLenTr ⟨17, by decide⟩ 23 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 23 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_17_24 (hp : 24 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 24 (transLenTr ⟨17, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 24 (transLenTr ⟨17, by decide⟩ 24 hp)) T141_17
      hfix141_17 hinj141_17 hcardT141_17
      (fun i => conj_mem_of_fixedPoints _ _ (T141_17 i) (hfix141_17 i) _)
      ⟨141, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 24 hp) Q2.T141_17_2 Q2.hfix141_17_2 Q2.hinj141_17_2
      Q2.hcardT141_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_17_2 i) (Q2.hfix141_17_2 i) _)
      colCert_141_17_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_0 (hp : 0 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 0 (transLenTr ⟨18, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 0 (transLenTr ⟨18, by decide⟩ 0 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 0 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_1 (hp : 1 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 1 (transLenTr ⟨18, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 1 (transLenTr ⟨18, by decide⟩ 1 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 1 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_2 (hp : 2 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 2 (transLenTr ⟨18, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 2 (transLenTr ⟨18, by decide⟩ 2 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 2 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_3 (hp : 3 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 3 (transLenTr ⟨18, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 3 (transLenTr ⟨18, by decide⟩ 3 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 3 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_4 (hp : 4 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 4 (transLenTr ⟨18, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 4 (transLenTr ⟨18, by decide⟩ 4 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 4 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_5 (hp : 5 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 5 (transLenTr ⟨18, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 5 (transLenTr ⟨18, by decide⟩ 5 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 5 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_6 (hp : 6 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 6 (transLenTr ⟨18, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 6 (transLenTr ⟨18, by decide⟩ 6 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 6 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_7 (hp : 7 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 7 (transLenTr ⟨18, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 7 (transLenTr ⟨18, by decide⟩ 7 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 7 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_8 (hp : 8 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 8 (transLenTr ⟨18, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 8 (transLenTr ⟨18, by decide⟩ 8 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 8 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_9 (hp : 9 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 9 (transLenTr ⟨18, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 9 (transLenTr ⟨18, by decide⟩ 9 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 9 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_10 (hp : 10 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 10 (transLenTr ⟨18, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 10 (transLenTr ⟨18, by decide⟩ 10 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 10 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_11 (hp : 11 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 11 (transLenTr ⟨18, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 11 (transLenTr ⟨18, by decide⟩ 11 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 11 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_12 (hp : 12 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 12 (transLenTr ⟨18, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 12 (transLenTr ⟨18, by decide⟩ 12 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 12 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_13 (hp : 13 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 13 (transLenTr ⟨18, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 13 (transLenTr ⟨18, by decide⟩ 13 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 13 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_14 (hp : 14 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 14 (transLenTr ⟨18, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 14 (transLenTr ⟨18, by decide⟩ 14 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 14 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_15 (hp : 15 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 15 (transLenTr ⟨18, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 15 (transLenTr ⟨18, by decide⟩ 15 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 15 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_16 (hp : 16 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 16 (transLenTr ⟨18, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 16 (transLenTr ⟨18, by decide⟩ 16 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 16 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_17 (hp : 17 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 17 (transLenTr ⟨18, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 17 (transLenTr ⟨18, by decide⟩ 17 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 17 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_18 (hp : 18 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 18 (transLenTr ⟨18, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 18 (transLenTr ⟨18, by decide⟩ 18 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 18 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_19 (hp : 19 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 19 (transLenTr ⟨18, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 19 (transLenTr ⟨18, by decide⟩ 19 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 19 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_20 (hp : 20 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 20 (transLenTr ⟨18, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 20 (transLenTr ⟨18, by decide⟩ 20 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 20 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_21 (hp : 21 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 21 (transLenTr ⟨18, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 21 (transLenTr ⟨18, by decide⟩ 21 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 21 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_22 (hp : 22 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 22 (transLenTr ⟨18, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 22 (transLenTr ⟨18, by decide⟩ 22 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 22 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_23 (hp : 23 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 23 (transLenTr ⟨18, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 23 (transLenTr ⟨18, by decide⟩ 23 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 23 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_23.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_18_24 (hp : 24 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 24 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 24 (transLenTr ⟨18, by decide⟩ 24 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 24 (transLenTr ⟨18, by decide⟩ 24 hp)) T141_18
      hfix141_18 hinj141_18 hcardT141_18
      (fun i => conj_mem_of_fixedPoints _ _ (T141_18 i) (hfix141_18 i) _)
      ⟨141, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 24 hp) Q2.T141_18_2 Q2.hfix141_18_2 Q2.hinj141_18_2
      Q2.hcardT141_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_18_2 i) (Q2.hfix141_18_2 i) _)
      colCert_141_18_24.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T141_19
      hfix141_19 hinj141_19 hcardT141_19
      (fun i => conj_mem_of_fixedPoints _ _ (T141_19 i) (hfix141_19 i) _)
      ⟨141, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T141_19_2 Q2.hfix141_19_2 Q2.hinj141_19_2
      Q2.hcardT141_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_19_2 i) (Q2.hfix141_19_2 i) _)
      colCert_141_19_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T141_19
      hfix141_19 hinj141_19 hcardT141_19
      (fun i => conj_mem_of_fixedPoints _ _ (T141_19 i) (hfix141_19 i) _)
      ⟨141, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T141_19_2 Q2.hfix141_19_2 Q2.hinj141_19_2
      Q2.hcardT141_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_19_2 i) (Q2.hfix141_19_2 i) _)
      colCert_141_19_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T141_19
      hfix141_19 hinj141_19 hcardT141_19
      (fun i => conj_mem_of_fixedPoints _ _ (T141_19 i) (hfix141_19 i) _)
      ⟨141, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T141_19_2 Q2.hfix141_19_2 Q2.hinj141_19_2
      Q2.hcardT141_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_19_2 i) (Q2.hfix141_19_2 i) _)
      colCert_141_19_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T141_19
      hfix141_19 hinj141_19 hcardT141_19
      (fun i => conj_mem_of_fixedPoints _ _ (T141_19 i) (hfix141_19 i) _)
      ⟨141, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T141_19_2 Q2.hfix141_19_2 Q2.hinj141_19_2
      Q2.hcardT141_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_19_2 i) (Q2.hfix141_19_2 i) _)
      colCert_141_19_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T141_19
      hfix141_19 hinj141_19 hcardT141_19
      (fun i => conj_mem_of_fixedPoints _ _ (T141_19 i) (hfix141_19 i) _)
      ⟨141, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T141_19_2 Q2.hfix141_19_2 Q2.hinj141_19_2
      Q2.hcardT141_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_19_2 i) (Q2.hfix141_19_2 i) _)
      colCert_141_19_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T141_19
      hfix141_19 hinj141_19 hcardT141_19
      (fun i => conj_mem_of_fixedPoints _ _ (T141_19 i) (hfix141_19 i) _)
      ⟨141, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T141_19_2 Q2.hfix141_19_2 Q2.hinj141_19_2
      Q2.hcardT141_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_19_2 i) (Q2.hfix141_19_2 i) _)
      colCert_141_19_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T141_19
      hfix141_19 hinj141_19 hcardT141_19
      (fun i => conj_mem_of_fixedPoints _ _ (T141_19 i) (hfix141_19 i) _)
      ⟨141, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T141_19_2 Q2.hfix141_19_2 Q2.hinj141_19_2
      Q2.hcardT141_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_19_2 i) (Q2.hfix141_19_2 i) _)
      colCert_141_19_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T141_19
      hfix141_19 hinj141_19 hcardT141_19
      (fun i => conj_mem_of_fixedPoints _ _ (T141_19 i) (hfix141_19 i) _)
      ⟨141, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T141_19_2 Q2.hfix141_19_2 Q2.hinj141_19_2
      Q2.hcardT141_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_19_2 i) (Q2.hfix141_19_2 i) _)
      colCert_141_19_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T141_19
      hfix141_19 hinj141_19 hcardT141_19
      (fun i => conj_mem_of_fixedPoints _ _ (T141_19 i) (hfix141_19 i) _)
      ⟨141, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T141_19_2 Q2.hfix141_19_2 Q2.hinj141_19_2
      Q2.hcardT141_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_19_2 i) (Q2.hfix141_19_2 i) _)
      colCert_141_19_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T141_20
      hfix141_20 hinj141_20 hcardT141_20
      (fun i => conj_mem_of_fixedPoints _ _ (T141_20 i) (hfix141_20 i) _)
      ⟨141, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T141_20_2 Q2.hfix141_20_2 Q2.hinj141_20_2
      Q2.hcardT141_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_20_2 i) (Q2.hfix141_20_2 i) _)
      colCert_141_20_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T141_20
      hfix141_20 hinj141_20 hcardT141_20
      (fun i => conj_mem_of_fixedPoints _ _ (T141_20 i) (hfix141_20 i) _)
      ⟨141, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T141_20_2 Q2.hfix141_20_2 Q2.hinj141_20_2
      Q2.hcardT141_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_20_2 i) (Q2.hfix141_20_2 i) _)
      colCert_141_20_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T141_20
      hfix141_20 hinj141_20 hcardT141_20
      (fun i => conj_mem_of_fixedPoints _ _ (T141_20 i) (hfix141_20 i) _)
      ⟨141, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T141_20_2 Q2.hfix141_20_2 Q2.hinj141_20_2
      Q2.hcardT141_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_20_2 i) (Q2.hfix141_20_2 i) _)
      colCert_141_20_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T141_20
      hfix141_20 hinj141_20 hcardT141_20
      (fun i => conj_mem_of_fixedPoints _ _ (T141_20 i) (hfix141_20 i) _)
      ⟨141, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T141_20_2 Q2.hfix141_20_2 Q2.hinj141_20_2
      Q2.hcardT141_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_20_2 i) (Q2.hfix141_20_2 i) _)
      colCert_141_20_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T141_20
      hfix141_20 hinj141_20 hcardT141_20
      (fun i => conj_mem_of_fixedPoints _ _ (T141_20 i) (hfix141_20 i) _)
      ⟨141, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T141_20_2 Q2.hfix141_20_2 Q2.hinj141_20_2
      Q2.hcardT141_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_20_2 i) (Q2.hfix141_20_2 i) _)
      colCert_141_20_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T141_20
      hfix141_20 hinj141_20 hcardT141_20
      (fun i => conj_mem_of_fixedPoints _ _ (T141_20 i) (hfix141_20 i) _)
      ⟨141, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T141_20_2 Q2.hfix141_20_2 Q2.hinj141_20_2
      Q2.hcardT141_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_20_2 i) (Q2.hfix141_20_2 i) _)
      colCert_141_20_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T141_20
      hfix141_20 hinj141_20 hcardT141_20
      (fun i => conj_mem_of_fixedPoints _ _ (T141_20 i) (hfix141_20 i) _)
      ⟨141, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T141_20_2 Q2.hfix141_20_2 Q2.hinj141_20_2
      Q2.hcardT141_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_20_2 i) (Q2.hfix141_20_2 i) _)
      colCert_141_20_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T141_20
      hfix141_20 hinj141_20 hcardT141_20
      (fun i => conj_mem_of_fixedPoints _ _ (T141_20 i) (hfix141_20 i) _)
      ⟨141, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T141_20_2 Q2.hfix141_20_2 Q2.hinj141_20_2
      Q2.hcardT141_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_20_2 i) (Q2.hfix141_20_2 i) _)
      colCert_141_20_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T141_20
      hfix141_20 hinj141_20 hcardT141_20
      (fun i => conj_mem_of_fixedPoints _ _ (T141_20 i) (hfix141_20 i) _)
      ⟨141, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T141_20_2 Q2.hfix141_20_2 Q2.hinj141_20_2
      Q2.hcardT141_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_20_2 i) (Q2.hfix141_20_2 i) _)
      colCert_141_20_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T141_21
      hfix141_21 hinj141_21 hcardT141_21
      (fun i => conj_mem_of_fixedPoints _ _ (T141_21 i) (hfix141_21 i) _)
      ⟨141, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T141_21_2 Q2.hfix141_21_2 Q2.hinj141_21_2
      Q2.hcardT141_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_21_2 i) (Q2.hfix141_21_2 i) _)
      colCert_141_21_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T141_21
      hfix141_21 hinj141_21 hcardT141_21
      (fun i => conj_mem_of_fixedPoints _ _ (T141_21 i) (hfix141_21 i) _)
      ⟨141, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T141_21_2 Q2.hfix141_21_2 Q2.hinj141_21_2
      Q2.hcardT141_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_21_2 i) (Q2.hfix141_21_2 i) _)
      colCert_141_21_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T141_21
      hfix141_21 hinj141_21 hcardT141_21
      (fun i => conj_mem_of_fixedPoints _ _ (T141_21 i) (hfix141_21 i) _)
      ⟨141, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T141_21_2 Q2.hfix141_21_2 Q2.hinj141_21_2
      Q2.hcardT141_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_21_2 i) (Q2.hfix141_21_2 i) _)
      colCert_141_21_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T141_21
      hfix141_21 hinj141_21 hcardT141_21
      (fun i => conj_mem_of_fixedPoints _ _ (T141_21 i) (hfix141_21 i) _)
      ⟨141, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T141_21_2 Q2.hfix141_21_2 Q2.hinj141_21_2
      Q2.hcardT141_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_21_2 i) (Q2.hfix141_21_2 i) _)
      colCert_141_21_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T141_21
      hfix141_21 hinj141_21 hcardT141_21
      (fun i => conj_mem_of_fixedPoints _ _ (T141_21 i) (hfix141_21 i) _)
      ⟨141, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T141_21_2 Q2.hfix141_21_2 Q2.hinj141_21_2
      Q2.hcardT141_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_21_2 i) (Q2.hfix141_21_2 i) _)
      colCert_141_21_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T141_21
      hfix141_21 hinj141_21 hcardT141_21
      (fun i => conj_mem_of_fixedPoints _ _ (T141_21 i) (hfix141_21 i) _)
      ⟨141, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T141_21_2 Q2.hfix141_21_2 Q2.hinj141_21_2
      Q2.hcardT141_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_21_2 i) (Q2.hfix141_21_2 i) _)
      colCert_141_21_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T141_21
      hfix141_21 hinj141_21 hcardT141_21
      (fun i => conj_mem_of_fixedPoints _ _ (T141_21 i) (hfix141_21 i) _)
      ⟨141, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T141_21_2 Q2.hfix141_21_2 Q2.hinj141_21_2
      Q2.hcardT141_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_21_2 i) (Q2.hfix141_21_2 i) _)
      colCert_141_21_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T141_21
      hfix141_21 hinj141_21 hcardT141_21
      (fun i => conj_mem_of_fixedPoints _ _ (T141_21 i) (hfix141_21 i) _)
      ⟨141, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T141_21_2 Q2.hfix141_21_2 Q2.hinj141_21_2
      Q2.hcardT141_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_21_2 i) (Q2.hfix141_21_2 i) _)
      colCert_141_21_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T141_21
      hfix141_21 hinj141_21 hcardT141_21
      (fun i => conj_mem_of_fixedPoints _ _ (T141_21 i) (hfix141_21 i) _)
      ⟨141, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T141_21_2 Q2.hfix141_21_2 Q2.hinj141_21_2
      Q2.hcardT141_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_21_2 i) (Q2.hfix141_21_2 i) _)
      colCert_141_21_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T141_22
      hfix141_22 hinj141_22 hcardT141_22
      (fun i => conj_mem_of_fixedPoints _ _ (T141_22 i) (hfix141_22 i) _)
      ⟨141, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T141_22_2 Q2.hfix141_22_2 Q2.hinj141_22_2
      Q2.hcardT141_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_22_2 i) (Q2.hfix141_22_2 i) _)
      colCert_141_22_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T141_22
      hfix141_22 hinj141_22 hcardT141_22
      (fun i => conj_mem_of_fixedPoints _ _ (T141_22 i) (hfix141_22 i) _)
      ⟨141, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T141_22_2 Q2.hfix141_22_2 Q2.hinj141_22_2
      Q2.hcardT141_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_22_2 i) (Q2.hfix141_22_2 i) _)
      colCert_141_22_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T141_22
      hfix141_22 hinj141_22 hcardT141_22
      (fun i => conj_mem_of_fixedPoints _ _ (T141_22 i) (hfix141_22 i) _)
      ⟨141, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T141_22_2 Q2.hfix141_22_2 Q2.hinj141_22_2
      Q2.hcardT141_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_22_2 i) (Q2.hfix141_22_2 i) _)
      colCert_141_22_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T141_22
      hfix141_22 hinj141_22 hcardT141_22
      (fun i => conj_mem_of_fixedPoints _ _ (T141_22 i) (hfix141_22 i) _)
      ⟨141, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T141_22_2 Q2.hfix141_22_2 Q2.hinj141_22_2
      Q2.hcardT141_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_22_2 i) (Q2.hfix141_22_2 i) _)
      colCert_141_22_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T141_22
      hfix141_22 hinj141_22 hcardT141_22
      (fun i => conj_mem_of_fixedPoints _ _ (T141_22 i) (hfix141_22 i) _)
      ⟨141, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T141_22_2 Q2.hfix141_22_2 Q2.hinj141_22_2
      Q2.hcardT141_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_22_2 i) (Q2.hfix141_22_2 i) _)
      colCert_141_22_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T141_22
      hfix141_22 hinj141_22 hcardT141_22
      (fun i => conj_mem_of_fixedPoints _ _ (T141_22 i) (hfix141_22 i) _)
      ⟨141, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T141_22_2 Q2.hfix141_22_2 Q2.hinj141_22_2
      Q2.hcardT141_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_22_2 i) (Q2.hfix141_22_2 i) _)
      colCert_141_22_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T141_22
      hfix141_22 hinj141_22 hcardT141_22
      (fun i => conj_mem_of_fixedPoints _ _ (T141_22 i) (hfix141_22 i) _)
      ⟨141, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T141_22_2 Q2.hfix141_22_2 Q2.hinj141_22_2
      Q2.hcardT141_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_22_2 i) (Q2.hfix141_22_2 i) _)
      colCert_141_22_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T141_22
      hfix141_22 hinj141_22 hcardT141_22
      (fun i => conj_mem_of_fixedPoints _ _ (T141_22 i) (hfix141_22 i) _)
      ⟨141, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T141_22_2 Q2.hfix141_22_2 Q2.hinj141_22_2
      Q2.hcardT141_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_22_2 i) (Q2.hfix141_22_2 i) _)
      colCert_141_22_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T141_22
      hfix141_22 hinj141_22 hcardT141_22
      (fun i => conj_mem_of_fixedPoints _ _ (T141_22 i) (hfix141_22 i) _)
      ⟨141, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T141_22_2 Q2.hfix141_22_2 Q2.hinj141_22_2
      Q2.hcardT141_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_22_2 i) (Q2.hfix141_22_2 i) _)
      colCert_141_22_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T141_23
      hfix141_23 hinj141_23 hcardT141_23
      (fun i => conj_mem_of_fixedPoints _ _ (T141_23 i) (hfix141_23 i) _)
      ⟨141, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T141_23_2 Q2.hfix141_23_2 Q2.hinj141_23_2
      Q2.hcardT141_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_23_2 i) (Q2.hfix141_23_2 i) _)
      colCert_141_23_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T141_23
      hfix141_23 hinj141_23 hcardT141_23
      (fun i => conj_mem_of_fixedPoints _ _ (T141_23 i) (hfix141_23 i) _)
      ⟨141, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T141_23_2 Q2.hfix141_23_2 Q2.hinj141_23_2
      Q2.hcardT141_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_23_2 i) (Q2.hfix141_23_2 i) _)
      colCert_141_23_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T141_23
      hfix141_23 hinj141_23 hcardT141_23
      (fun i => conj_mem_of_fixedPoints _ _ (T141_23 i) (hfix141_23 i) _)
      ⟨141, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T141_23_2 Q2.hfix141_23_2 Q2.hinj141_23_2
      Q2.hcardT141_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_23_2 i) (Q2.hfix141_23_2 i) _)
      colCert_141_23_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T141_23
      hfix141_23 hinj141_23 hcardT141_23
      (fun i => conj_mem_of_fixedPoints _ _ (T141_23 i) (hfix141_23 i) _)
      ⟨141, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T141_23_2 Q2.hfix141_23_2 Q2.hinj141_23_2
      Q2.hcardT141_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_23_2 i) (Q2.hfix141_23_2 i) _)
      colCert_141_23_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T141_23
      hfix141_23 hinj141_23 hcardT141_23
      (fun i => conj_mem_of_fixedPoints _ _ (T141_23 i) (hfix141_23 i) _)
      ⟨141, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T141_23_2 Q2.hfix141_23_2 Q2.hinj141_23_2
      Q2.hcardT141_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_23_2 i) (Q2.hfix141_23_2 i) _)
      colCert_141_23_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T141_23
      hfix141_23 hinj141_23 hcardT141_23
      (fun i => conj_mem_of_fixedPoints _ _ (T141_23 i) (hfix141_23 i) _)
      ⟨141, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T141_23_2 Q2.hfix141_23_2 Q2.hinj141_23_2
      Q2.hcardT141_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_23_2 i) (Q2.hfix141_23_2 i) _)
      colCert_141_23_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T141_23
      hfix141_23 hinj141_23 hcardT141_23
      (fun i => conj_mem_of_fixedPoints _ _ (T141_23 i) (hfix141_23 i) _)
      ⟨141, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T141_23_2 Q2.hfix141_23_2 Q2.hinj141_23_2
      Q2.hcardT141_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_23_2 i) (Q2.hfix141_23_2 i) _)
      colCert_141_23_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T141_23
      hfix141_23 hinj141_23 hcardT141_23
      (fun i => conj_mem_of_fixedPoints _ _ (T141_23 i) (hfix141_23 i) _)
      ⟨141, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T141_23_2 Q2.hfix141_23_2 Q2.hinj141_23_2
      Q2.hcardT141_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_23_2 i) (Q2.hfix141_23_2 i) _)
      colCert_141_23_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T141_23
      hfix141_23 hinj141_23 hcardT141_23
      (fun i => conj_mem_of_fixedPoints _ _ (T141_23 i) (hfix141_23 i) _)
      ⟨141, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T141_23_2 Q2.hfix141_23_2 Q2.hinj141_23_2
      Q2.hcardT141_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_23_2 i) (Q2.hfix141_23_2 i) _)
      colCert_141_23_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T141_24
      hfix141_24 hinj141_24 hcardT141_24
      (fun i => conj_mem_of_fixedPoints _ _ (T141_24 i) (hfix141_24 i) _)
      ⟨141, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T141_24_2 Q2.hfix141_24_2 Q2.hinj141_24_2
      Q2.hcardT141_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_24_2 i) (Q2.hfix141_24_2 i) _)
      colCert_141_24_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T141_24
      hfix141_24 hinj141_24 hcardT141_24
      (fun i => conj_mem_of_fixedPoints _ _ (T141_24 i) (hfix141_24 i) _)
      ⟨141, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T141_24_2 Q2.hfix141_24_2 Q2.hinj141_24_2
      Q2.hcardT141_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_24_2 i) (Q2.hfix141_24_2 i) _)
      colCert_141_24_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T141_24
      hfix141_24 hinj141_24 hcardT141_24
      (fun i => conj_mem_of_fixedPoints _ _ (T141_24 i) (hfix141_24 i) _)
      ⟨141, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T141_24_2 Q2.hfix141_24_2 Q2.hinj141_24_2
      Q2.hcardT141_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_24_2 i) (Q2.hfix141_24_2 i) _)
      colCert_141_24_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T141_24
      hfix141_24 hinj141_24 hcardT141_24
      (fun i => conj_mem_of_fixedPoints _ _ (T141_24 i) (hfix141_24 i) _)
      ⟨141, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T141_24_2 Q2.hfix141_24_2 Q2.hinj141_24_2
      Q2.hcardT141_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_24_2 i) (Q2.hfix141_24_2 i) _)
      colCert_141_24_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T141_24
      hfix141_24 hinj141_24 hcardT141_24
      (fun i => conj_mem_of_fixedPoints _ _ (T141_24 i) (hfix141_24 i) _)
      ⟨141, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T141_24_2 Q2.hfix141_24_2 Q2.hinj141_24_2
      Q2.hcardT141_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_24_2 i) (Q2.hfix141_24_2 i) _)
      colCert_141_24_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T141_24
      hfix141_24 hinj141_24 hcardT141_24
      (fun i => conj_mem_of_fixedPoints _ _ (T141_24 i) (hfix141_24 i) _)
      ⟨141, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T141_24_2 Q2.hfix141_24_2 Q2.hinj141_24_2
      Q2.hcardT141_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_24_2 i) (Q2.hfix141_24_2 i) _)
      colCert_141_24_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T141_24
      hfix141_24 hinj141_24 hcardT141_24
      (fun i => conj_mem_of_fixedPoints _ _ (T141_24 i) (hfix141_24 i) _)
      ⟨141, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T141_24_2 Q2.hfix141_24_2 Q2.hinj141_24_2
      Q2.hcardT141_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_24_2 i) (Q2.hfix141_24_2 i) _)
      colCert_141_24_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T141_24
      hfix141_24 hinj141_24 hcardT141_24
      (fun i => conj_mem_of_fixedPoints _ _ (T141_24 i) (hfix141_24 i) _)
      ⟨141, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T141_24_2 Q2.hfix141_24_2 Q2.hinj141_24_2
      Q2.hcardT141_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_24_2 i) (Q2.hfix141_24_2 i) _)
      colCert_141_24_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T141_24
      hfix141_24 hinj141_24 hcardT141_24
      (fun i => conj_mem_of_fixedPoints _ _ (T141_24 i) (hfix141_24 i) _)
      ⟨141, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T141_24_2 Q2.hfix141_24_2 Q2.hinj141_24_2
      Q2.hcardT141_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_24_2 i) (Q2.hfix141_24_2 i) _)
      colCert_141_24_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T141_25
      hfix141_25 hinj141_25 hcardT141_25
      (fun i => conj_mem_of_fixedPoints _ _ (T141_25 i) (hfix141_25 i) _)
      ⟨141, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T141_25_2 Q2.hfix141_25_2 Q2.hinj141_25_2
      Q2.hcardT141_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_25_2 i) (Q2.hfix141_25_2 i) _)
      colCert_141_25_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T141_25
      hfix141_25 hinj141_25 hcardT141_25
      (fun i => conj_mem_of_fixedPoints _ _ (T141_25 i) (hfix141_25 i) _)
      ⟨141, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T141_25_2 Q2.hfix141_25_2 Q2.hinj141_25_2
      Q2.hcardT141_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_25_2 i) (Q2.hfix141_25_2 i) _)
      colCert_141_25_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T141_25
      hfix141_25 hinj141_25 hcardT141_25
      (fun i => conj_mem_of_fixedPoints _ _ (T141_25 i) (hfix141_25 i) _)
      ⟨141, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T141_25_2 Q2.hfix141_25_2 Q2.hinj141_25_2
      Q2.hcardT141_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_25_2 i) (Q2.hfix141_25_2 i) _)
      colCert_141_25_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T141_25
      hfix141_25 hinj141_25 hcardT141_25
      (fun i => conj_mem_of_fixedPoints _ _ (T141_25 i) (hfix141_25 i) _)
      ⟨141, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T141_25_2 Q2.hfix141_25_2 Q2.hinj141_25_2
      Q2.hcardT141_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_25_2 i) (Q2.hfix141_25_2 i) _)
      colCert_141_25_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T141_25
      hfix141_25 hinj141_25 hcardT141_25
      (fun i => conj_mem_of_fixedPoints _ _ (T141_25 i) (hfix141_25 i) _)
      ⟨141, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T141_25_2 Q2.hfix141_25_2 Q2.hinj141_25_2
      Q2.hcardT141_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_25_2 i) (Q2.hfix141_25_2 i) _)
      colCert_141_25_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T141_25
      hfix141_25 hinj141_25 hcardT141_25
      (fun i => conj_mem_of_fixedPoints _ _ (T141_25 i) (hfix141_25 i) _)
      ⟨141, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T141_25_2 Q2.hfix141_25_2 Q2.hinj141_25_2
      Q2.hcardT141_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_25_2 i) (Q2.hfix141_25_2 i) _)
      colCert_141_25_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T141_25
      hfix141_25 hinj141_25 hcardT141_25
      (fun i => conj_mem_of_fixedPoints _ _ (T141_25 i) (hfix141_25 i) _)
      ⟨141, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T141_25_2 Q2.hfix141_25_2 Q2.hinj141_25_2
      Q2.hcardT141_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_25_2 i) (Q2.hfix141_25_2 i) _)
      colCert_141_25_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T141_25
      hfix141_25 hinj141_25 hcardT141_25
      (fun i => conj_mem_of_fixedPoints _ _ (T141_25 i) (hfix141_25 i) _)
      ⟨141, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T141_25_2 Q2.hfix141_25_2 Q2.hinj141_25_2
      Q2.hcardT141_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_25_2 i) (Q2.hfix141_25_2 i) _)
      colCert_141_25_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T141_25
      hfix141_25 hinj141_25 hcardT141_25
      (fun i => conj_mem_of_fixedPoints _ _ (T141_25 i) (hfix141_25 i) _)
      ⟨141, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T141_25_2 Q2.hfix141_25_2 Q2.hinj141_25_2
      Q2.hcardT141_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_25_2 i) (Q2.hfix141_25_2 i) _)
      colCert_141_25_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T141_26
      hfix141_26 hinj141_26 hcardT141_26
      (fun i => conj_mem_of_fixedPoints _ _ (T141_26 i) (hfix141_26 i) _)
      ⟨141, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T141_26_2 Q2.hfix141_26_2 Q2.hinj141_26_2
      Q2.hcardT141_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_26_2 i) (Q2.hfix141_26_2 i) _)
      colCert_141_26_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T141_26
      hfix141_26 hinj141_26 hcardT141_26
      (fun i => conj_mem_of_fixedPoints _ _ (T141_26 i) (hfix141_26 i) _)
      ⟨141, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T141_26_2 Q2.hfix141_26_2 Q2.hinj141_26_2
      Q2.hcardT141_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_26_2 i) (Q2.hfix141_26_2 i) _)
      colCert_141_26_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T141_26
      hfix141_26 hinj141_26 hcardT141_26
      (fun i => conj_mem_of_fixedPoints _ _ (T141_26 i) (hfix141_26 i) _)
      ⟨141, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T141_26_2 Q2.hfix141_26_2 Q2.hinj141_26_2
      Q2.hcardT141_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_26_2 i) (Q2.hfix141_26_2 i) _)
      colCert_141_26_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T141_26
      hfix141_26 hinj141_26 hcardT141_26
      (fun i => conj_mem_of_fixedPoints _ _ (T141_26 i) (hfix141_26 i) _)
      ⟨141, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T141_26_2 Q2.hfix141_26_2 Q2.hinj141_26_2
      Q2.hcardT141_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_26_2 i) (Q2.hfix141_26_2 i) _)
      colCert_141_26_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T141_26
      hfix141_26 hinj141_26 hcardT141_26
      (fun i => conj_mem_of_fixedPoints _ _ (T141_26 i) (hfix141_26 i) _)
      ⟨141, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T141_26_2 Q2.hfix141_26_2 Q2.hinj141_26_2
      Q2.hcardT141_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_26_2 i) (Q2.hfix141_26_2 i) _)
      colCert_141_26_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T141_26
      hfix141_26 hinj141_26 hcardT141_26
      (fun i => conj_mem_of_fixedPoints _ _ (T141_26 i) (hfix141_26 i) _)
      ⟨141, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T141_26_2 Q2.hfix141_26_2 Q2.hinj141_26_2
      Q2.hcardT141_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_26_2 i) (Q2.hfix141_26_2 i) _)
      colCert_141_26_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T141_26
      hfix141_26 hinj141_26 hcardT141_26
      (fun i => conj_mem_of_fixedPoints _ _ (T141_26 i) (hfix141_26 i) _)
      ⟨141, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T141_26_2 Q2.hfix141_26_2 Q2.hinj141_26_2
      Q2.hcardT141_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_26_2 i) (Q2.hfix141_26_2 i) _)
      colCert_141_26_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T141_26
      hfix141_26 hinj141_26 hcardT141_26
      (fun i => conj_mem_of_fixedPoints _ _ (T141_26 i) (hfix141_26 i) _)
      ⟨141, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T141_26_2 Q2.hfix141_26_2 Q2.hinj141_26_2
      Q2.hcardT141_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_26_2 i) (Q2.hfix141_26_2 i) _)
      colCert_141_26_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T141_26
      hfix141_26 hinj141_26 hcardT141_26
      (fun i => conj_mem_of_fixedPoints _ _ (T141_26 i) (hfix141_26 i) _)
      ⟨141, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T141_26_2 Q2.hfix141_26_2 Q2.hinj141_26_2
      Q2.hcardT141_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_26_2 i) (Q2.hfix141_26_2 i) _)
      colCert_141_26_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T141_27
      hfix141_27 hinj141_27 hcardT141_27
      (fun i => conj_mem_of_fixedPoints _ _ (T141_27 i) (hfix141_27 i) _)
      ⟨141, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T141_27_2 Q2.hfix141_27_2 Q2.hinj141_27_2
      Q2.hcardT141_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_27_2 i) (Q2.hfix141_27_2 i) _)
      colCert_141_27_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T141_27
      hfix141_27 hinj141_27 hcardT141_27
      (fun i => conj_mem_of_fixedPoints _ _ (T141_27 i) (hfix141_27 i) _)
      ⟨141, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T141_27_2 Q2.hfix141_27_2 Q2.hinj141_27_2
      Q2.hcardT141_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_27_2 i) (Q2.hfix141_27_2 i) _)
      colCert_141_27_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T141_27
      hfix141_27 hinj141_27 hcardT141_27
      (fun i => conj_mem_of_fixedPoints _ _ (T141_27 i) (hfix141_27 i) _)
      ⟨141, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T141_27_2 Q2.hfix141_27_2 Q2.hinj141_27_2
      Q2.hcardT141_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_27_2 i) (Q2.hfix141_27_2 i) _)
      colCert_141_27_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T141_27
      hfix141_27 hinj141_27 hcardT141_27
      (fun i => conj_mem_of_fixedPoints _ _ (T141_27 i) (hfix141_27 i) _)
      ⟨141, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T141_27_2 Q2.hfix141_27_2 Q2.hinj141_27_2
      Q2.hcardT141_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_27_2 i) (Q2.hfix141_27_2 i) _)
      colCert_141_27_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T141_27
      hfix141_27 hinj141_27 hcardT141_27
      (fun i => conj_mem_of_fixedPoints _ _ (T141_27 i) (hfix141_27 i) _)
      ⟨141, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T141_27_2 Q2.hfix141_27_2 Q2.hinj141_27_2
      Q2.hcardT141_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_27_2 i) (Q2.hfix141_27_2 i) _)
      colCert_141_27_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T141_27
      hfix141_27 hinj141_27 hcardT141_27
      (fun i => conj_mem_of_fixedPoints _ _ (T141_27 i) (hfix141_27 i) _)
      ⟨141, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T141_27_2 Q2.hfix141_27_2 Q2.hinj141_27_2
      Q2.hcardT141_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_27_2 i) (Q2.hfix141_27_2 i) _)
      colCert_141_27_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T141_27
      hfix141_27 hinj141_27 hcardT141_27
      (fun i => conj_mem_of_fixedPoints _ _ (T141_27 i) (hfix141_27 i) _)
      ⟨141, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T141_27_2 Q2.hfix141_27_2 Q2.hinj141_27_2
      Q2.hcardT141_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_27_2 i) (Q2.hfix141_27_2 i) _)
      colCert_141_27_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T141_27
      hfix141_27 hinj141_27 hcardT141_27
      (fun i => conj_mem_of_fixedPoints _ _ (T141_27 i) (hfix141_27 i) _)
      ⟨141, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T141_27_2 Q2.hfix141_27_2 Q2.hinj141_27_2
      Q2.hcardT141_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_27_2 i) (Q2.hfix141_27_2 i) _)
      colCert_141_27_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T141_27
      hfix141_27 hinj141_27 hcardT141_27
      (fun i => conj_mem_of_fixedPoints _ _ (T141_27 i) (hfix141_27 i) _)
      ⟨141, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T141_27_2 Q2.hfix141_27_2 Q2.hinj141_27_2
      Q2.hcardT141_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_27_2 i) (Q2.hfix141_27_2 i) _)
      colCert_141_27_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T141_53
      hfix141_53 hinj141_53 hcardT141_53
      (fun i => conj_mem_of_fixedPoints _ _ (T141_53 i) (hfix141_53 i) _)
      ⟨141, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T141_53_2 Q2.hfix141_53_2 Q2.hinj141_53_2
      Q2.hcardT141_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_53_2 i) (Q2.hfix141_53_2 i) _)
      colCert_141_53_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T141_53
      hfix141_53 hinj141_53 hcardT141_53
      (fun i => conj_mem_of_fixedPoints _ _ (T141_53 i) (hfix141_53 i) _)
      ⟨141, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T141_53_2 Q2.hfix141_53_2 Q2.hinj141_53_2
      Q2.hcardT141_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_53_2 i) (Q2.hfix141_53_2 i) _)
      colCert_141_53_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T141_53
      hfix141_53 hinj141_53 hcardT141_53
      (fun i => conj_mem_of_fixedPoints _ _ (T141_53 i) (hfix141_53 i) _)
      ⟨141, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T141_53_2 Q2.hfix141_53_2 Q2.hinj141_53_2
      Q2.hcardT141_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_53_2 i) (Q2.hfix141_53_2 i) _)
      colCert_141_53_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T141_53
      hfix141_53 hinj141_53 hcardT141_53
      (fun i => conj_mem_of_fixedPoints _ _ (T141_53 i) (hfix141_53 i) _)
      ⟨141, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T141_53_2 Q2.hfix141_53_2 Q2.hinj141_53_2
      Q2.hcardT141_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_53_2 i) (Q2.hfix141_53_2 i) _)
      colCert_141_53_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T141_53
      hfix141_53 hinj141_53 hcardT141_53
      (fun i => conj_mem_of_fixedPoints _ _ (T141_53 i) (hfix141_53 i) _)
      ⟨141, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T141_53_2 Q2.hfix141_53_2 Q2.hinj141_53_2
      Q2.hcardT141_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_53_2 i) (Q2.hfix141_53_2 i) _)
      colCert_141_53_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T141_53
      hfix141_53 hinj141_53 hcardT141_53
      (fun i => conj_mem_of_fixedPoints _ _ (T141_53 i) (hfix141_53 i) _)
      ⟨141, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T141_53_2 Q2.hfix141_53_2 Q2.hinj141_53_2
      Q2.hcardT141_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_53_2 i) (Q2.hfix141_53_2 i) _)
      colCert_141_53_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T141_53
      hfix141_53 hinj141_53 hcardT141_53
      (fun i => conj_mem_of_fixedPoints _ _ (T141_53 i) (hfix141_53 i) _)
      ⟨141, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T141_53_2 Q2.hfix141_53_2 Q2.hinj141_53_2
      Q2.hcardT141_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_53_2 i) (Q2.hfix141_53_2 i) _)
      colCert_141_53_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T141_53
      hfix141_53 hinj141_53 hcardT141_53
      (fun i => conj_mem_of_fixedPoints _ _ (T141_53 i) (hfix141_53 i) _)
      ⟨141, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T141_53_2 Q2.hfix141_53_2 Q2.hinj141_53_2
      Q2.hcardT141_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_53_2 i) (Q2.hfix141_53_2 i) _)
      colCert_141_53_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T141_53
      hfix141_53 hinj141_53 hcardT141_53
      (fun i => conj_mem_of_fixedPoints _ _ (T141_53 i) (hfix141_53 i) _)
      ⟨141, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T141_53_2 Q2.hfix141_53_2 Q2.hinj141_53_2
      Q2.hcardT141_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_53_2 i) (Q2.hfix141_53_2 i) _)
      colCert_141_53_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T141_54
      hfix141_54 hinj141_54 hcardT141_54
      (fun i => conj_mem_of_fixedPoints _ _ (T141_54 i) (hfix141_54 i) _)
      ⟨141, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T141_54_2 Q2.hfix141_54_2 Q2.hinj141_54_2
      Q2.hcardT141_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_54_2 i) (Q2.hfix141_54_2 i) _)
      colCert_141_54_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T141_54
      hfix141_54 hinj141_54 hcardT141_54
      (fun i => conj_mem_of_fixedPoints _ _ (T141_54 i) (hfix141_54 i) _)
      ⟨141, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T141_54_2 Q2.hfix141_54_2 Q2.hinj141_54_2
      Q2.hcardT141_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_54_2 i) (Q2.hfix141_54_2 i) _)
      colCert_141_54_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T141_54
      hfix141_54 hinj141_54 hcardT141_54
      (fun i => conj_mem_of_fixedPoints _ _ (T141_54 i) (hfix141_54 i) _)
      ⟨141, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T141_54_2 Q2.hfix141_54_2 Q2.hinj141_54_2
      Q2.hcardT141_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_54_2 i) (Q2.hfix141_54_2 i) _)
      colCert_141_54_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T141_54
      hfix141_54 hinj141_54 hcardT141_54
      (fun i => conj_mem_of_fixedPoints _ _ (T141_54 i) (hfix141_54 i) _)
      ⟨141, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T141_54_2 Q2.hfix141_54_2 Q2.hinj141_54_2
      Q2.hcardT141_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_54_2 i) (Q2.hfix141_54_2 i) _)
      colCert_141_54_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T141_54
      hfix141_54 hinj141_54 hcardT141_54
      (fun i => conj_mem_of_fixedPoints _ _ (T141_54 i) (hfix141_54 i) _)
      ⟨141, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T141_54_2 Q2.hfix141_54_2 Q2.hinj141_54_2
      Q2.hcardT141_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_54_2 i) (Q2.hfix141_54_2 i) _)
      colCert_141_54_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T141_54
      hfix141_54 hinj141_54 hcardT141_54
      (fun i => conj_mem_of_fixedPoints _ _ (T141_54 i) (hfix141_54 i) _)
      ⟨141, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T141_54_2 Q2.hfix141_54_2 Q2.hinj141_54_2
      Q2.hcardT141_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_54_2 i) (Q2.hfix141_54_2 i) _)
      colCert_141_54_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T141_54
      hfix141_54 hinj141_54 hcardT141_54
      (fun i => conj_mem_of_fixedPoints _ _ (T141_54 i) (hfix141_54 i) _)
      ⟨141, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T141_54_2 Q2.hfix141_54_2 Q2.hinj141_54_2
      Q2.hcardT141_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_54_2 i) (Q2.hfix141_54_2 i) _)
      colCert_141_54_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T141_54
      hfix141_54 hinj141_54 hcardT141_54
      (fun i => conj_mem_of_fixedPoints _ _ (T141_54 i) (hfix141_54 i) _)
      ⟨141, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T141_54_2 Q2.hfix141_54_2 Q2.hinj141_54_2
      Q2.hcardT141_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_54_2 i) (Q2.hfix141_54_2 i) _)
      colCert_141_54_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T141_54
      hfix141_54 hinj141_54 hcardT141_54
      (fun i => conj_mem_of_fixedPoints _ _ (T141_54 i) (hfix141_54 i) _)
      ⟨141, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T141_54_2 Q2.hfix141_54_2 Q2.hinj141_54_2
      Q2.hcardT141_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_54_2 i) (Q2.hfix141_54_2 i) _)
      colCert_141_54_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_0 (hp : 0 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 0 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_1 (hp : 1 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 1 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_2 (hp : 2 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 2 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_3 (hp : 3 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 3 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_4 (hp : 4 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 4 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_5 (hp : 5 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 5 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_10 (hp : 10 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 10 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_15 (hp : 15 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 15 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_20 (hp : 20 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 20 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_25 (hp : 25 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 25 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 25 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_25.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_30 (hp : 30 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 30 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 30 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_30.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_35 (hp : 35 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 35 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 35 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_35.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_40 (hp : 40 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 40 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 40 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_40.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_45 (hp : 45 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 45 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 45 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_45.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_50 (hp : 50 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 50 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 50 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_50.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_55 (hp : 55 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 55 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 55 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_55.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_60 (hp : 60 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 60 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 60 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_60.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_65 (hp : 65 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 65 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 65 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_65.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_70 (hp : 70 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 70 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 70 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_70.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_75 (hp : 75 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 75 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 75 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_75.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_80 (hp : 80 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 80 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 80 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_80.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_85 (hp : 85 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 85 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 85 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_85.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_90 (hp : 90 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 90 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 90 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_90.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_95 (hp : 95 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 95 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 95 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_95.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_100 (hp : 100 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 100 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 100 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_100.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_105 (hp : 105 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 105 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 105 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_105.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_110 (hp : 110 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 110 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 110 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_110.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_115 (hp : 115 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 115 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 115 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_115.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_80_120 (hp : 120 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 120 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp)) T141_80
      hfix141_80 hinj141_80 hcardT141_80
      (fun i => conj_mem_of_fixedPoints _ _ (T141_80 i) (hfix141_80 i) _)
      ⟨141, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 120 hp) Q2.T141_80_2 Q2.hfix141_80_2 Q2.hinj141_80_2
      Q2.hcardT141_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_80_2 i) (Q2.hfix141_80_2 i) _)
      colCert_141_80_120.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_81_0 (hp : 0 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 0 (transLenTr ⟨81, by decide⟩ 0 hp)) T141_81
      hfix141_81 hinj141_81 hcardT141_81
      (fun i => conj_mem_of_fixedPoints _ _ (T141_81 i) (hfix141_81 i) _)
      ⟨141, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 0 hp) Q2.T141_81_2 Q2.hfix141_81_2 Q2.hinj141_81_2
      Q2.hcardT141_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_81_2 i) (Q2.hfix141_81_2 i) _)
      colCert_141_81_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_81_1 (hp : 1 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 1 (transLenTr ⟨81, by decide⟩ 1 hp)) T141_81
      hfix141_81 hinj141_81 hcardT141_81
      (fun i => conj_mem_of_fixedPoints _ _ (T141_81 i) (hfix141_81 i) _)
      ⟨141, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 1 hp) Q2.T141_81_2 Q2.hfix141_81_2 Q2.hinj141_81_2
      Q2.hcardT141_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_81_2 i) (Q2.hfix141_81_2 i) _)
      colCert_141_81_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_81_2 (hp : 2 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 2 (transLenTr ⟨81, by decide⟩ 2 hp)) T141_81
      hfix141_81 hinj141_81 hcardT141_81
      (fun i => conj_mem_of_fixedPoints _ _ (T141_81 i) (hfix141_81 i) _)
      ⟨141, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 2 hp) Q2.T141_81_2 Q2.hfix141_81_2 Q2.hinj141_81_2
      Q2.hcardT141_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_81_2 i) (Q2.hfix141_81_2 i) _)
      colCert_141_81_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_81_3 (hp : 3 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 3 (transLenTr ⟨81, by decide⟩ 3 hp)) T141_81
      hfix141_81 hinj141_81 hcardT141_81
      (fun i => conj_mem_of_fixedPoints _ _ (T141_81 i) (hfix141_81 i) _)
      ⟨141, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 3 hp) Q2.T141_81_2 Q2.hfix141_81_2 Q2.hinj141_81_2
      Q2.hcardT141_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_81_2 i) (Q2.hfix141_81_2 i) _)
      colCert_141_81_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_81_4 (hp : 4 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 4 (transLenTr ⟨81, by decide⟩ 4 hp)) T141_81
      hfix141_81 hinj141_81 hcardT141_81
      (fun i => conj_mem_of_fixedPoints _ _ (T141_81 i) (hfix141_81 i) _)
      ⟨141, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 4 hp) Q2.T141_81_2 Q2.hfix141_81_2 Q2.hinj141_81_2
      Q2.hcardT141_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_81_2 i) (Q2.hfix141_81_2 i) _)
      colCert_141_81_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_81_5 (hp : 5 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 5 (transLenTr ⟨81, by decide⟩ 5 hp)) T141_81
      hfix141_81 hinj141_81 hcardT141_81
      (fun i => conj_mem_of_fixedPoints _ _ (T141_81 i) (hfix141_81 i) _)
      ⟨141, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 5 hp) Q2.T141_81_2 Q2.hfix141_81_2 Q2.hinj141_81_2
      Q2.hcardT141_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_81_2 i) (Q2.hfix141_81_2 i) _)
      colCert_141_81_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_81_10 (hp : 10 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 10 (transLenTr ⟨81, by decide⟩ 10 hp)) T141_81
      hfix141_81 hinj141_81 hcardT141_81
      (fun i => conj_mem_of_fixedPoints _ _ (T141_81 i) (hfix141_81 i) _)
      ⟨141, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 10 hp) Q2.T141_81_2 Q2.hfix141_81_2 Q2.hinj141_81_2
      Q2.hcardT141_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_81_2 i) (Q2.hfix141_81_2 i) _)
      colCert_141_81_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_81_15 (hp : 15 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 15 (transLenTr ⟨81, by decide⟩ 15 hp)) T141_81
      hfix141_81 hinj141_81 hcardT141_81
      (fun i => conj_mem_of_fixedPoints _ _ (T141_81 i) (hfix141_81 i) _)
      ⟨141, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 15 hp) Q2.T141_81_2 Q2.hfix141_81_2 Q2.hinj141_81_2
      Q2.hcardT141_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_81_2 i) (Q2.hfix141_81_2 i) _)
      colCert_141_81_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_81_20 (hp : 20 < (Q2.transData.getD 81 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨81, by decide⟩ : Fin 148)) (colE2 ⟨81, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨81, by decide⟩ : Fin 148))
        (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨81, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨81, by decide⟩ 20 (transLenTr ⟨81, by decide⟩ 20 hp)) T141_81
      hfix141_81 hinj141_81 hcardT141_81
      (fun i => conj_mem_of_fixedPoints _ _ (T141_81 i) (hfix141_81 i) _)
      ⟨141, by decide⟩ ⟨81, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨81, by decide⟩ 20 hp) Q2.T141_81_2 Q2.hfix141_81_2 Q2.hinj141_81_2
      Q2.hcardT141_81_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_81_2 i) (Q2.hfix141_81_2 i) _)
      colCert_141_81_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_82_0 (hp : 0 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 0 (transLenTr ⟨82, by decide⟩ 0 hp)) T141_82
      hfix141_82 hinj141_82 hcardT141_82
      (fun i => conj_mem_of_fixedPoints _ _ (T141_82 i) (hfix141_82 i) _)
      ⟨141, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 0 hp) Q2.T141_82_2 Q2.hfix141_82_2 Q2.hinj141_82_2
      Q2.hcardT141_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_82_2 i) (Q2.hfix141_82_2 i) _)
      colCert_141_82_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_82_1 (hp : 1 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 1 (transLenTr ⟨82, by decide⟩ 1 hp)) T141_82
      hfix141_82 hinj141_82 hcardT141_82
      (fun i => conj_mem_of_fixedPoints _ _ (T141_82 i) (hfix141_82 i) _)
      ⟨141, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 1 hp) Q2.T141_82_2 Q2.hfix141_82_2 Q2.hinj141_82_2
      Q2.hcardT141_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_82_2 i) (Q2.hfix141_82_2 i) _)
      colCert_141_82_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_82_2 (hp : 2 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 2 (transLenTr ⟨82, by decide⟩ 2 hp)) T141_82
      hfix141_82 hinj141_82 hcardT141_82
      (fun i => conj_mem_of_fixedPoints _ _ (T141_82 i) (hfix141_82 i) _)
      ⟨141, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 2 hp) Q2.T141_82_2 Q2.hfix141_82_2 Q2.hinj141_82_2
      Q2.hcardT141_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_82_2 i) (Q2.hfix141_82_2 i) _)
      colCert_141_82_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_82_3 (hp : 3 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 3 (transLenTr ⟨82, by decide⟩ 3 hp)) T141_82
      hfix141_82 hinj141_82 hcardT141_82
      (fun i => conj_mem_of_fixedPoints _ _ (T141_82 i) (hfix141_82 i) _)
      ⟨141, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 3 hp) Q2.T141_82_2 Q2.hfix141_82_2 Q2.hinj141_82_2
      Q2.hcardT141_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_82_2 i) (Q2.hfix141_82_2 i) _)
      colCert_141_82_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_82_4 (hp : 4 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 4 (transLenTr ⟨82, by decide⟩ 4 hp)) T141_82
      hfix141_82 hinj141_82 hcardT141_82
      (fun i => conj_mem_of_fixedPoints _ _ (T141_82 i) (hfix141_82 i) _)
      ⟨141, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 4 hp) Q2.T141_82_2 Q2.hfix141_82_2 Q2.hinj141_82_2
      Q2.hcardT141_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_82_2 i) (Q2.hfix141_82_2 i) _)
      colCert_141_82_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_82_5 (hp : 5 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 5 (transLenTr ⟨82, by decide⟩ 5 hp)) T141_82
      hfix141_82 hinj141_82 hcardT141_82
      (fun i => conj_mem_of_fixedPoints _ _ (T141_82 i) (hfix141_82 i) _)
      ⟨141, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 5 hp) Q2.T141_82_2 Q2.hfix141_82_2 Q2.hinj141_82_2
      Q2.hcardT141_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_82_2 i) (Q2.hfix141_82_2 i) _)
      colCert_141_82_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_82_10 (hp : 10 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 10 (transLenTr ⟨82, by decide⟩ 10 hp)) T141_82
      hfix141_82 hinj141_82 hcardT141_82
      (fun i => conj_mem_of_fixedPoints _ _ (T141_82 i) (hfix141_82 i) _)
      ⟨141, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 10 hp) Q2.T141_82_2 Q2.hfix141_82_2 Q2.hinj141_82_2
      Q2.hcardT141_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_82_2 i) (Q2.hfix141_82_2 i) _)
      colCert_141_82_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_82_15 (hp : 15 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 15 (transLenTr ⟨82, by decide⟩ 15 hp)) T141_82
      hfix141_82 hinj141_82 hcardT141_82
      (fun i => conj_mem_of_fixedPoints _ _ (T141_82 i) (hfix141_82 i) _)
      ⟨141, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 15 hp) Q2.T141_82_2 Q2.hfix141_82_2 Q2.hinj141_82_2
      Q2.hcardT141_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_82_2 i) (Q2.hfix141_82_2 i) _)
      colCert_141_82_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_82_20 (hp : 20 < (Q2.transData.getD 82 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨82, by decide⟩ : Fin 148)) (colE2 ⟨82, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨82, by decide⟩ : Fin 148))
        (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨82, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨82, by decide⟩ 20 (transLenTr ⟨82, by decide⟩ 20 hp)) T141_82
      hfix141_82 hinj141_82 hcardT141_82
      (fun i => conj_mem_of_fixedPoints _ _ (T141_82 i) (hfix141_82 i) _)
      ⟨141, by decide⟩ ⟨82, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨82, by decide⟩ 20 hp) Q2.T141_82_2 Q2.hfix141_82_2 Q2.hinj141_82_2
      Q2.hcardT141_82_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_82_2 i) (Q2.hfix141_82_2 i) _)
      colCert_141_82_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_83_0 (hp : 0 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 0 (transLenTr ⟨83, by decide⟩ 0 hp)) T141_83
      hfix141_83 hinj141_83 hcardT141_83
      (fun i => conj_mem_of_fixedPoints _ _ (T141_83 i) (hfix141_83 i) _)
      ⟨141, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 0 hp) Q2.T141_83_2 Q2.hfix141_83_2 Q2.hinj141_83_2
      Q2.hcardT141_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_83_2 i) (Q2.hfix141_83_2 i) _)
      colCert_141_83_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_83_1 (hp : 1 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 1 (transLenTr ⟨83, by decide⟩ 1 hp)) T141_83
      hfix141_83 hinj141_83 hcardT141_83
      (fun i => conj_mem_of_fixedPoints _ _ (T141_83 i) (hfix141_83 i) _)
      ⟨141, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 1 hp) Q2.T141_83_2 Q2.hfix141_83_2 Q2.hinj141_83_2
      Q2.hcardT141_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_83_2 i) (Q2.hfix141_83_2 i) _)
      colCert_141_83_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_83_2 (hp : 2 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 2 (transLenTr ⟨83, by decide⟩ 2 hp)) T141_83
      hfix141_83 hinj141_83 hcardT141_83
      (fun i => conj_mem_of_fixedPoints _ _ (T141_83 i) (hfix141_83 i) _)
      ⟨141, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 2 hp) Q2.T141_83_2 Q2.hfix141_83_2 Q2.hinj141_83_2
      Q2.hcardT141_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_83_2 i) (Q2.hfix141_83_2 i) _)
      colCert_141_83_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_83_3 (hp : 3 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 3 (transLenTr ⟨83, by decide⟩ 3 hp)) T141_83
      hfix141_83 hinj141_83 hcardT141_83
      (fun i => conj_mem_of_fixedPoints _ _ (T141_83 i) (hfix141_83 i) _)
      ⟨141, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 3 hp) Q2.T141_83_2 Q2.hfix141_83_2 Q2.hinj141_83_2
      Q2.hcardT141_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_83_2 i) (Q2.hfix141_83_2 i) _)
      colCert_141_83_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_83_4 (hp : 4 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 4 (transLenTr ⟨83, by decide⟩ 4 hp)) T141_83
      hfix141_83 hinj141_83 hcardT141_83
      (fun i => conj_mem_of_fixedPoints _ _ (T141_83 i) (hfix141_83 i) _)
      ⟨141, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 4 hp) Q2.T141_83_2 Q2.hfix141_83_2 Q2.hinj141_83_2
      Q2.hcardT141_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_83_2 i) (Q2.hfix141_83_2 i) _)
      colCert_141_83_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_83_5 (hp : 5 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 5 (transLenTr ⟨83, by decide⟩ 5 hp)) T141_83
      hfix141_83 hinj141_83 hcardT141_83
      (fun i => conj_mem_of_fixedPoints _ _ (T141_83 i) (hfix141_83 i) _)
      ⟨141, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 5 hp) Q2.T141_83_2 Q2.hfix141_83_2 Q2.hinj141_83_2
      Q2.hcardT141_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_83_2 i) (Q2.hfix141_83_2 i) _)
      colCert_141_83_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_83_10 (hp : 10 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 10 (transLenTr ⟨83, by decide⟩ 10 hp)) T141_83
      hfix141_83 hinj141_83 hcardT141_83
      (fun i => conj_mem_of_fixedPoints _ _ (T141_83 i) (hfix141_83 i) _)
      ⟨141, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 10 hp) Q2.T141_83_2 Q2.hfix141_83_2 Q2.hinj141_83_2
      Q2.hcardT141_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_83_2 i) (Q2.hfix141_83_2 i) _)
      colCert_141_83_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_83_15 (hp : 15 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 15 (transLenTr ⟨83, by decide⟩ 15 hp)) T141_83
      hfix141_83 hinj141_83 hcardT141_83
      (fun i => conj_mem_of_fixedPoints _ _ (T141_83 i) (hfix141_83 i) _)
      ⟨141, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 15 hp) Q2.T141_83_2 Q2.hfix141_83_2 Q2.hinj141_83_2
      Q2.hcardT141_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_83_2 i) (Q2.hfix141_83_2 i) _)
      colCert_141_83_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_83_20 (hp : 20 < (Q2.transData.getD 83 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨83, by decide⟩ : Fin 148)) (colE2 ⟨83, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨83, by decide⟩ : Fin 148))
        (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨83, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨83, by decide⟩ 20 (transLenTr ⟨83, by decide⟩ 20 hp)) T141_83
      hfix141_83 hinj141_83 hcardT141_83
      (fun i => conj_mem_of_fixedPoints _ _ (T141_83 i) (hfix141_83 i) _)
      ⟨141, by decide⟩ ⟨83, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨83, by decide⟩ 20 hp) Q2.T141_83_2 Q2.hfix141_83_2 Q2.hinj141_83_2
      Q2.hcardT141_83_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_83_2 i) (Q2.hfix141_83_2 i) _)
      colCert_141_83_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_84_0 (hp : 0 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 0 (transLenTr ⟨84, by decide⟩ 0 hp)) T141_84
      hfix141_84 hinj141_84 hcardT141_84
      (fun i => conj_mem_of_fixedPoints _ _ (T141_84 i) (hfix141_84 i) _)
      ⟨141, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 0 hp) Q2.T141_84_2 Q2.hfix141_84_2 Q2.hinj141_84_2
      Q2.hcardT141_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_84_2 i) (Q2.hfix141_84_2 i) _)
      colCert_141_84_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_84_1 (hp : 1 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 1 (transLenTr ⟨84, by decide⟩ 1 hp)) T141_84
      hfix141_84 hinj141_84 hcardT141_84
      (fun i => conj_mem_of_fixedPoints _ _ (T141_84 i) (hfix141_84 i) _)
      ⟨141, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 1 hp) Q2.T141_84_2 Q2.hfix141_84_2 Q2.hinj141_84_2
      Q2.hcardT141_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_84_2 i) (Q2.hfix141_84_2 i) _)
      colCert_141_84_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_84_2 (hp : 2 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 2 (transLenTr ⟨84, by decide⟩ 2 hp)) T141_84
      hfix141_84 hinj141_84 hcardT141_84
      (fun i => conj_mem_of_fixedPoints _ _ (T141_84 i) (hfix141_84 i) _)
      ⟨141, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 2 hp) Q2.T141_84_2 Q2.hfix141_84_2 Q2.hinj141_84_2
      Q2.hcardT141_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_84_2 i) (Q2.hfix141_84_2 i) _)
      colCert_141_84_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_84_3 (hp : 3 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 3 (transLenTr ⟨84, by decide⟩ 3 hp)) T141_84
      hfix141_84 hinj141_84 hcardT141_84
      (fun i => conj_mem_of_fixedPoints _ _ (T141_84 i) (hfix141_84 i) _)
      ⟨141, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 3 hp) Q2.T141_84_2 Q2.hfix141_84_2 Q2.hinj141_84_2
      Q2.hcardT141_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_84_2 i) (Q2.hfix141_84_2 i) _)
      colCert_141_84_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_84_4 (hp : 4 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 4 (transLenTr ⟨84, by decide⟩ 4 hp)) T141_84
      hfix141_84 hinj141_84 hcardT141_84
      (fun i => conj_mem_of_fixedPoints _ _ (T141_84 i) (hfix141_84 i) _)
      ⟨141, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 4 hp) Q2.T141_84_2 Q2.hfix141_84_2 Q2.hinj141_84_2
      Q2.hcardT141_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_84_2 i) (Q2.hfix141_84_2 i) _)
      colCert_141_84_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_84_5 (hp : 5 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 5 (transLenTr ⟨84, by decide⟩ 5 hp)) T141_84
      hfix141_84 hinj141_84 hcardT141_84
      (fun i => conj_mem_of_fixedPoints _ _ (T141_84 i) (hfix141_84 i) _)
      ⟨141, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 5 hp) Q2.T141_84_2 Q2.hfix141_84_2 Q2.hinj141_84_2
      Q2.hcardT141_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_84_2 i) (Q2.hfix141_84_2 i) _)
      colCert_141_84_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_84_10 (hp : 10 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 10 (transLenTr ⟨84, by decide⟩ 10 hp)) T141_84
      hfix141_84 hinj141_84 hcardT141_84
      (fun i => conj_mem_of_fixedPoints _ _ (T141_84 i) (hfix141_84 i) _)
      ⟨141, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 10 hp) Q2.T141_84_2 Q2.hfix141_84_2 Q2.hinj141_84_2
      Q2.hcardT141_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_84_2 i) (Q2.hfix141_84_2 i) _)
      colCert_141_84_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_84_15 (hp : 15 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 15 (transLenTr ⟨84, by decide⟩ 15 hp)) T141_84
      hfix141_84 hinj141_84 hcardT141_84
      (fun i => conj_mem_of_fixedPoints _ _ (T141_84 i) (hfix141_84 i) _)
      ⟨141, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 15 hp) Q2.T141_84_2 Q2.hfix141_84_2 Q2.hinj141_84_2
      Q2.hcardT141_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_84_2 i) (Q2.hfix141_84_2 i) _)
      colCert_141_84_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_84_20 (hp : 20 < (Q2.transData.getD 84 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨84, by decide⟩ : Fin 148)) (colE2 ⟨84, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨84, by decide⟩ : Fin 148))
        (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨84, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨84, by decide⟩ 20 (transLenTr ⟨84, by decide⟩ 20 hp)) T141_84
      hfix141_84 hinj141_84 hcardT141_84
      (fun i => conj_mem_of_fixedPoints _ _ (T141_84 i) (hfix141_84 i) _)
      ⟨141, by decide⟩ ⟨84, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨84, by decide⟩ 20 hp) Q2.T141_84_2 Q2.hfix141_84_2 Q2.hinj141_84_2
      Q2.hcardT141_84_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_84_2 i) (Q2.hfix141_84_2 i) _)
      colCert_141_84_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_0 (hp : 0 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 0 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 0 (transLenTr ⟨85, by decide⟩ 0 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 0 (transLenTr ⟨85, by decide⟩ 0 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 0 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_0.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_1 (hp : 1 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 1 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 1 (transLenTr ⟨85, by decide⟩ 1 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 1 (transLenTr ⟨85, by decide⟩ 1 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 1 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_1.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_2 (hp : 2 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 2 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 2 (transLenTr ⟨85, by decide⟩ 2 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 2 (transLenTr ⟨85, by decide⟩ 2 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 2 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_2.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_3 (hp : 3 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 3 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 3 (transLenTr ⟨85, by decide⟩ 3 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 3 (transLenTr ⟨85, by decide⟩ 3 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 3 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_3.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_4 (hp : 4 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 4 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 4 (transLenTr ⟨85, by decide⟩ 4 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 4 (transLenTr ⟨85, by decide⟩ 4 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 4 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_4.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_5 (hp : 5 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 5 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 5 (transLenTr ⟨85, by decide⟩ 5 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 5 (transLenTr ⟨85, by decide⟩ 5 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 5 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_5.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_6 (hp : 6 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 6 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 6 (transLenTr ⟨85, by decide⟩ 6 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 6 (transLenTr ⟨85, by decide⟩ 6 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 6 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_6.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_7 (hp : 7 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 7 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 7 (transLenTr ⟨85, by decide⟩ 7 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 7 (transLenTr ⟨85, by decide⟩ 7 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 7 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_7.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_8 (hp : 8 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 8 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 8 (transLenTr ⟨85, by decide⟩ 8 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 8 (transLenTr ⟨85, by decide⟩ 8 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 8 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_8.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_9 (hp : 9 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 9 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 9 (transLenTr ⟨85, by decide⟩ 9 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 9 (transLenTr ⟨85, by decide⟩ 9 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 9 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_9.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_10 (hp : 10 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 10 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 10 (transLenTr ⟨85, by decide⟩ 10 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 10 (transLenTr ⟨85, by decide⟩ 10 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 10 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_10.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_11 (hp : 11 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 11 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 11 (transLenTr ⟨85, by decide⟩ 11 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 11 (transLenTr ⟨85, by decide⟩ 11 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 11 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_11.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_12 (hp : 12 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 12 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 12 (transLenTr ⟨85, by decide⟩ 12 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 12 (transLenTr ⟨85, by decide⟩ 12 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 12 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_12.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_13 (hp : 13 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 13 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 13 (transLenTr ⟨85, by decide⟩ 13 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 13 (transLenTr ⟨85, by decide⟩ 13 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 13 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_13.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_14 (hp : 14 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 14 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 14 (transLenTr ⟨85, by decide⟩ 14 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 14 (transLenTr ⟨85, by decide⟩ 14 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 14 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_14.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_15 (hp : 15 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 15 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 15 (transLenTr ⟨85, by decide⟩ 15 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 15 (transLenTr ⟨85, by decide⟩ 15 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 15 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_15.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_16 (hp : 16 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 16 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 16 (transLenTr ⟨85, by decide⟩ 16 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 16 (transLenTr ⟨85, by decide⟩ 16 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 16 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_16.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_17 (hp : 17 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 17 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 17 (transLenTr ⟨85, by decide⟩ 17 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 17 (transLenTr ⟨85, by decide⟩ 17 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 17 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_17.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_18 (hp : 18 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 18 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 18 (transLenTr ⟨85, by decide⟩ 18 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 18 (transLenTr ⟨85, by decide⟩ 18 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 18 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_18.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_19 (hp : 19 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 19 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 19 (transLenTr ⟨85, by decide⟩ 19 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 19 (transLenTr ⟨85, by decide⟩ 19 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 19 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_19.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_20 (hp : 20 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 20 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 20 (transLenTr ⟨85, by decide⟩ 20 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 20 (transLenTr ⟨85, by decide⟩ 20 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 20 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_20.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_21 (hp : 21 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 21 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 21 (transLenTr ⟨85, by decide⟩ 21 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 21 (transLenTr ⟨85, by decide⟩ 21 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 21 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_21.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_22 (hp : 22 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 22 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 22 (transLenTr ⟨85, by decide⟩ 22 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 22 (transLenTr ⟨85, by decide⟩ 22 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 22 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_22.hD ?_).symm
  rw [alnId_141 j hj]


theorem leaf_141_85_23 (hp : 23 < (Q2.transData.getD 85 []).length)
    (j : Nat) (hj : j < (repChars.getD 141 []).length)
    (hq : (normIsRep.getD 141 []).getD j false = true) :
    species (Q2.reps (⟨85, by decide⟩ : Fin 148)) (colE2 ⟨85, by decide⟩ 23 hp)
        (rowE2 (⟨141, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨85, by decide⟩ : Fin 148))
        (colE1 ⟨85, by decide⟩ 23 (transLenTr ⟨85, by decide⟩ 23 hp))
        (rowE1 (⟨141, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨141, by decide⟩ : Fin 148) ⟨85, by decide⟩ _
      (validAt ⟨141, by decide⟩ (listedAt ⟨141, by decide⟩ hj))
      (colE1 ⟨85, by decide⟩ 23 (transLenTr ⟨85, by decide⟩ 23 hp)) T141_85
      hfix141_85 hinj141_85 hcardT141_85
      (fun i => conj_mem_of_fixedPoints _ _ (T141_85 i) (hfix141_85 i) _)
      ⟨141, by decide⟩ ⟨85, by decide⟩ _
      (Q2.validAt ⟨141, by decide⟩ (Q2.listedAt ⟨141, by decide⟩
        (alnCheck_rep ⟨141, by decide⟩ hj hq).1))
      (colE2 ⟨85, by decide⟩ 23 hp) Q2.T141_85_2 Q2.hfix141_85_2 Q2.hinj141_85_2
      Q2.hcardT141_85_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T141_85_2 i) (Q2.hfix141_85_2 i) _)
      colCert_141_85_23.hD ?_).symm
  rw [alnId_141 j hj]


end LeanDring.P5Presentation
