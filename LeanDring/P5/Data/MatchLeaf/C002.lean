/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColRestCheap.C001
import LeanDring.P5.Data.ColRestCheap.C002
import LeanDring.P5.Data.ColRestCheap.C003
import LeanDring.P5.Data.ColRestCheap.C004
import LeanDring.P5.Data.ColRestCheap.C005
import LeanDring.P5.Data.ColRestHeavy.C001
import LeanDring.P5.Data.ColRestHeavy.C002
import LeanDring.P5.Data.ColRestHeavy.C003
import LeanDring.P5.Data.ColRestHeavy.C004
import LeanDring.P5.Data.ColRestHeavy.C005
import LeanDring.P5.Data.ColRestHeavy.C006
import LeanDring.P5.Data.ColRestHeavy.C007
import LeanDring.P5.Data.ColRestHeavy.C008
import LeanDring.P5.Data.EntryA.C004
import LeanDring.P5.Data.EntryA.C005
import LeanDring.P5.Data.EntryA.C006
import LeanDring.P5.Data.EntryA.C007
import LeanDring.P5.Data.EntryA.C008
import LeanDring.P5.Data.EntryA.C009
import LeanDring.P5.Data.EntryA.C010
import LeanDring.P5.Data.EntryA.C011
import LeanDring.P5.Data.EntryA.C012
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore

/-! # Stage-5 leaves, chunk 1 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_16_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T16_11
      hfix16_11 hinj16_11 hcardT16_11
      (fun i => conj_mem_of_fixedPoints _ _ (T16_11 i) (hfix16_11 i) _)
      ⟨16, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T16_11_2 Q2.hfix16_11_2 Q2.hinj16_11_2
      Q2.hcardT16_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_11_2 i) (Q2.hfix16_11_2 i) _)
      colCert_16_11_0.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T16_11
      hfix16_11 hinj16_11 hcardT16_11
      (fun i => conj_mem_of_fixedPoints _ _ (T16_11 i) (hfix16_11 i) _)
      ⟨16, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T16_11_2 Q2.hfix16_11_2 Q2.hinj16_11_2
      Q2.hcardT16_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_11_2 i) (Q2.hfix16_11_2 i) _)
      colCert_16_11_1.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T16_11
      hfix16_11 hinj16_11 hcardT16_11
      (fun i => conj_mem_of_fixedPoints _ _ (T16_11 i) (hfix16_11 i) _)
      ⟨16, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T16_11_2 Q2.hfix16_11_2 Q2.hinj16_11_2
      Q2.hcardT16_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_11_2 i) (Q2.hfix16_11_2 i) _)
      colCert_16_11_2.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T16_11
      hfix16_11 hinj16_11 hcardT16_11
      (fun i => conj_mem_of_fixedPoints _ _ (T16_11 i) (hfix16_11 i) _)
      ⟨16, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T16_11_2 Q2.hfix16_11_2 Q2.hinj16_11_2
      Q2.hcardT16_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_11_2 i) (Q2.hfix16_11_2 i) _)
      colCert_16_11_3.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T16_11
      hfix16_11 hinj16_11 hcardT16_11
      (fun i => conj_mem_of_fixedPoints _ _ (T16_11 i) (hfix16_11 i) _)
      ⟨16, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T16_11_2 Q2.hfix16_11_2 Q2.hinj16_11_2
      Q2.hcardT16_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_11_2 i) (Q2.hfix16_11_2 i) _)
      colCert_16_11_4.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_0 (hp : 0 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 0 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 0 (transLenTr ⟨16, by decide⟩ 0 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 0 (transLenTr ⟨16, by decide⟩ 0 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 0 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_0.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_1 (hp : 1 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 1 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 1 (transLenTr ⟨16, by decide⟩ 1 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 1 (transLenTr ⟨16, by decide⟩ 1 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 1 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_1.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_2 (hp : 2 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 2 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 2 (transLenTr ⟨16, by decide⟩ 2 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 2 (transLenTr ⟨16, by decide⟩ 2 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 2 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_2.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_3 (hp : 3 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 3 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 3 (transLenTr ⟨16, by decide⟩ 3 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 3 (transLenTr ⟨16, by decide⟩ 3 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 3 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_3.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_4 (hp : 4 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 4 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 4 (transLenTr ⟨16, by decide⟩ 4 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 4 (transLenTr ⟨16, by decide⟩ 4 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 4 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_4.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_5 (hp : 5 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 5 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 5 (transLenTr ⟨16, by decide⟩ 5 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 5 (transLenTr ⟨16, by decide⟩ 5 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 5 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_5.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_6 (hp : 6 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 6 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 6 (transLenTr ⟨16, by decide⟩ 6 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 6 (transLenTr ⟨16, by decide⟩ 6 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 6 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_6.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_7 (hp : 7 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 7 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 7 (transLenTr ⟨16, by decide⟩ 7 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 7 (transLenTr ⟨16, by decide⟩ 7 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 7 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_7.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_8 (hp : 8 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 8 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 8 (transLenTr ⟨16, by decide⟩ 8 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 8 (transLenTr ⟨16, by decide⟩ 8 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 8 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_8.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_9 (hp : 9 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 9 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 9 (transLenTr ⟨16, by decide⟩ 9 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 9 (transLenTr ⟨16, by decide⟩ 9 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 9 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_9.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_10 (hp : 10 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 10 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 10 (transLenTr ⟨16, by decide⟩ 10 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 10 (transLenTr ⟨16, by decide⟩ 10 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 10 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_10.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_11 (hp : 11 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 11 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 11 (transLenTr ⟨16, by decide⟩ 11 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 11 (transLenTr ⟨16, by decide⟩ 11 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 11 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_11.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_12 (hp : 12 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 12 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 12 (transLenTr ⟨16, by decide⟩ 12 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 12 (transLenTr ⟨16, by decide⟩ 12 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 12 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_12.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_13 (hp : 13 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 13 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 13 (transLenTr ⟨16, by decide⟩ 13 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 13 (transLenTr ⟨16, by decide⟩ 13 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 13 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_13.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_14 (hp : 14 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 14 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 14 (transLenTr ⟨16, by decide⟩ 14 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 14 (transLenTr ⟨16, by decide⟩ 14 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 14 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_14.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_15 (hp : 15 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 15 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 15 (transLenTr ⟨16, by decide⟩ 15 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 15 (transLenTr ⟨16, by decide⟩ 15 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 15 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_15.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_16 (hp : 16 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 16 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 16 (transLenTr ⟨16, by decide⟩ 16 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 16 (transLenTr ⟨16, by decide⟩ 16 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 16 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_16.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_17 (hp : 17 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 17 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 17 (transLenTr ⟨16, by decide⟩ 17 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 17 (transLenTr ⟨16, by decide⟩ 17 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 17 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_17.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_18 (hp : 18 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 18 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 18 (transLenTr ⟨16, by decide⟩ 18 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 18 (transLenTr ⟨16, by decide⟩ 18 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 18 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_18.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_19 (hp : 19 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 19 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 19 (transLenTr ⟨16, by decide⟩ 19 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 19 (transLenTr ⟨16, by decide⟩ 19 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 19 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_19.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_20 (hp : 20 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 20 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 20 (transLenTr ⟨16, by decide⟩ 20 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 20 (transLenTr ⟨16, by decide⟩ 20 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 20 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_20.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_21 (hp : 21 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 21 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 21 (transLenTr ⟨16, by decide⟩ 21 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 21 (transLenTr ⟨16, by decide⟩ 21 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 21 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_21.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_22 (hp : 22 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 22 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 22 (transLenTr ⟨16, by decide⟩ 22 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 22 (transLenTr ⟨16, by decide⟩ 22 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 22 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_22.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_23 (hp : 23 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 23 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 23 (transLenTr ⟨16, by decide⟩ 23 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 23 (transLenTr ⟨16, by decide⟩ 23 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 23 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_23.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_16_16_24 (hp : 24 < (Q2.transData.getD 16 []).length)
    (j : Nat) (hj : j < (repChars.getD 16 []).length)
    (hq : (normIsRep.getD 16 []).getD j false = true) :
    species (Q2.reps (⟨16, by decide⟩ : Fin 148)) (colE2 ⟨16, by decide⟩ 24 hp)
        (rowE2 (⟨16, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨16, by decide⟩ : Fin 148))
        (colE1 ⟨16, by decide⟩ 24 (transLenTr ⟨16, by decide⟩ 24 hp))
        (rowE1 (⟨16, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨16, by decide⟩ : Fin 148) ⟨16, by decide⟩ _
      (validAt ⟨16, by decide⟩ (listedAt ⟨16, by decide⟩ hj))
      (colE1 ⟨16, by decide⟩ 24 (transLenTr ⟨16, by decide⟩ 24 hp)) T16_16
      hfix16_16 hinj16_16 hcardT16_16
      (fun i => conj_mem_of_fixedPoints _ _ (T16_16 i) (hfix16_16 i) _)
      ⟨16, by decide⟩ ⟨16, by decide⟩ _
      (Q2.validAt ⟨16, by decide⟩ (Q2.listedAt ⟨16, by decide⟩
        (alnCheck_rep ⟨16, by decide⟩ hj hq).1))
      (colE2 ⟨16, by decide⟩ 24 hp) Q2.T16_16_2 Q2.hfix16_16_2 Q2.hinj16_16_2
      Q2.hcardT16_16_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T16_16_2 i) (Q2.hfix16_16_2 i) _)
      colCert_16_16_24.hD ?_).symm
  rw [alnId_16 j hj]


theorem leaf_17_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T17_2
      hfix17_2 hinj17_2 hcardT17_2
      (fun i => conj_mem_of_fixedPoints _ _ (T17_2 i) (hfix17_2 i) _)
      ⟨17, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T17_2_2 Q2.hfix17_2_2 Q2.hinj17_2_2
      Q2.hcardT17_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_2_2 i) (Q2.hfix17_2_2 i) _)
      colCert_17_2_0.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T17_2
      hfix17_2 hinj17_2 hcardT17_2
      (fun i => conj_mem_of_fixedPoints _ _ (T17_2 i) (hfix17_2 i) _)
      ⟨17, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T17_2_2 Q2.hfix17_2_2 Q2.hinj17_2_2
      Q2.hcardT17_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_2_2 i) (Q2.hfix17_2_2 i) _)
      colCert_17_2_1.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T17_2
      hfix17_2 hinj17_2 hcardT17_2
      (fun i => conj_mem_of_fixedPoints _ _ (T17_2 i) (hfix17_2 i) _)
      ⟨17, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T17_2_2 Q2.hfix17_2_2 Q2.hinj17_2_2
      Q2.hcardT17_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_2_2 i) (Q2.hfix17_2_2 i) _)
      colCert_17_2_2.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T17_2
      hfix17_2 hinj17_2 hcardT17_2
      (fun i => conj_mem_of_fixedPoints _ _ (T17_2 i) (hfix17_2 i) _)
      ⟨17, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T17_2_2 Q2.hfix17_2_2 Q2.hinj17_2_2
      Q2.hcardT17_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_2_2 i) (Q2.hfix17_2_2 i) _)
      colCert_17_2_3.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T17_2
      hfix17_2 hinj17_2 hcardT17_2
      (fun i => conj_mem_of_fixedPoints _ _ (T17_2 i) (hfix17_2 i) _)
      ⟨17, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T17_2_2 Q2.hfix17_2_2 Q2.hinj17_2_2
      Q2.hcardT17_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_2_2 i) (Q2.hfix17_2_2 i) _)
      colCert_17_2_4.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T17_3
      hfix17_3 hinj17_3 hcardT17_3
      (fun i => conj_mem_of_fixedPoints _ _ (T17_3 i) (hfix17_3 i) _)
      ⟨17, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T17_3_2 Q2.hfix17_3_2 Q2.hinj17_3_2
      Q2.hcardT17_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_3_2 i) (Q2.hfix17_3_2 i) _)
      colCert_17_3_0.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T17_3
      hfix17_3 hinj17_3 hcardT17_3
      (fun i => conj_mem_of_fixedPoints _ _ (T17_3 i) (hfix17_3 i) _)
      ⟨17, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T17_3_2 Q2.hfix17_3_2 Q2.hinj17_3_2
      Q2.hcardT17_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_3_2 i) (Q2.hfix17_3_2 i) _)
      colCert_17_3_1.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T17_3
      hfix17_3 hinj17_3 hcardT17_3
      (fun i => conj_mem_of_fixedPoints _ _ (T17_3 i) (hfix17_3 i) _)
      ⟨17, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T17_3_2 Q2.hfix17_3_2 Q2.hinj17_3_2
      Q2.hcardT17_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_3_2 i) (Q2.hfix17_3_2 i) _)
      colCert_17_3_2.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T17_3
      hfix17_3 hinj17_3 hcardT17_3
      (fun i => conj_mem_of_fixedPoints _ _ (T17_3 i) (hfix17_3 i) _)
      ⟨17, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T17_3_2 Q2.hfix17_3_2 Q2.hinj17_3_2
      Q2.hcardT17_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_3_2 i) (Q2.hfix17_3_2 i) _)
      colCert_17_3_3.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T17_3
      hfix17_3 hinj17_3 hcardT17_3
      (fun i => conj_mem_of_fixedPoints _ _ (T17_3 i) (hfix17_3 i) _)
      ⟨17, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T17_3_2 Q2.hfix17_3_2 Q2.hinj17_3_2
      Q2.hcardT17_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_3_2 i) (Q2.hfix17_3_2 i) _)
      colCert_17_3_4.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T17_4
      hfix17_4 hinj17_4 hcardT17_4
      (fun i => conj_mem_of_fixedPoints _ _ (T17_4 i) (hfix17_4 i) _)
      ⟨17, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T17_4_2 Q2.hfix17_4_2 Q2.hinj17_4_2
      Q2.hcardT17_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_4_2 i) (Q2.hfix17_4_2 i) _)
      colCert_17_4_0.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T17_4
      hfix17_4 hinj17_4 hcardT17_4
      (fun i => conj_mem_of_fixedPoints _ _ (T17_4 i) (hfix17_4 i) _)
      ⟨17, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T17_4_2 Q2.hfix17_4_2 Q2.hinj17_4_2
      Q2.hcardT17_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_4_2 i) (Q2.hfix17_4_2 i) _)
      colCert_17_4_1.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T17_4
      hfix17_4 hinj17_4 hcardT17_4
      (fun i => conj_mem_of_fixedPoints _ _ (T17_4 i) (hfix17_4 i) _)
      ⟨17, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T17_4_2 Q2.hfix17_4_2 Q2.hinj17_4_2
      Q2.hcardT17_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_4_2 i) (Q2.hfix17_4_2 i) _)
      colCert_17_4_2.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T17_4
      hfix17_4 hinj17_4 hcardT17_4
      (fun i => conj_mem_of_fixedPoints _ _ (T17_4 i) (hfix17_4 i) _)
      ⟨17, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T17_4_2 Q2.hfix17_4_2 Q2.hinj17_4_2
      Q2.hcardT17_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_4_2 i) (Q2.hfix17_4_2 i) _)
      colCert_17_4_3.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T17_4
      hfix17_4 hinj17_4 hcardT17_4
      (fun i => conj_mem_of_fixedPoints _ _ (T17_4 i) (hfix17_4 i) _)
      ⟨17, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T17_4_2 Q2.hfix17_4_2 Q2.hinj17_4_2
      Q2.hcardT17_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_4_2 i) (Q2.hfix17_4_2 i) _)
      colCert_17_4_4.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T17_5
      hfix17_5 hinj17_5 hcardT17_5
      (fun i => conj_mem_of_fixedPoints _ _ (T17_5 i) (hfix17_5 i) _)
      ⟨17, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T17_5_2 Q2.hfix17_5_2 Q2.hinj17_5_2
      Q2.hcardT17_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_5_2 i) (Q2.hfix17_5_2 i) _)
      colCert_17_5_0.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T17_5
      hfix17_5 hinj17_5 hcardT17_5
      (fun i => conj_mem_of_fixedPoints _ _ (T17_5 i) (hfix17_5 i) _)
      ⟨17, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T17_5_2 Q2.hfix17_5_2 Q2.hinj17_5_2
      Q2.hcardT17_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_5_2 i) (Q2.hfix17_5_2 i) _)
      colCert_17_5_1.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T17_5
      hfix17_5 hinj17_5 hcardT17_5
      (fun i => conj_mem_of_fixedPoints _ _ (T17_5 i) (hfix17_5 i) _)
      ⟨17, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T17_5_2 Q2.hfix17_5_2 Q2.hinj17_5_2
      Q2.hcardT17_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_5_2 i) (Q2.hfix17_5_2 i) _)
      colCert_17_5_2.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T17_5
      hfix17_5 hinj17_5 hcardT17_5
      (fun i => conj_mem_of_fixedPoints _ _ (T17_5 i) (hfix17_5 i) _)
      ⟨17, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T17_5_2 Q2.hfix17_5_2 Q2.hinj17_5_2
      Q2.hcardT17_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_5_2 i) (Q2.hfix17_5_2 i) _)
      colCert_17_5_3.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T17_5
      hfix17_5 hinj17_5 hcardT17_5
      (fun i => conj_mem_of_fixedPoints _ _ (T17_5 i) (hfix17_5 i) _)
      ⟨17, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T17_5_2 Q2.hfix17_5_2 Q2.hinj17_5_2
      Q2.hcardT17_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_5_2 i) (Q2.hfix17_5_2 i) _)
      colCert_17_5_4.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T17_9
      hfix17_9 hinj17_9 hcardT17_9
      (fun i => conj_mem_of_fixedPoints _ _ (T17_9 i) (hfix17_9 i) _)
      ⟨17, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T17_9_2 Q2.hfix17_9_2 Q2.hinj17_9_2
      Q2.hcardT17_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_9_2 i) (Q2.hfix17_9_2 i) _)
      colCert_17_9_0.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T17_9
      hfix17_9 hinj17_9 hcardT17_9
      (fun i => conj_mem_of_fixedPoints _ _ (T17_9 i) (hfix17_9 i) _)
      ⟨17, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T17_9_2 Q2.hfix17_9_2 Q2.hinj17_9_2
      Q2.hcardT17_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_9_2 i) (Q2.hfix17_9_2 i) _)
      colCert_17_9_1.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T17_9
      hfix17_9 hinj17_9 hcardT17_9
      (fun i => conj_mem_of_fixedPoints _ _ (T17_9 i) (hfix17_9 i) _)
      ⟨17, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T17_9_2 Q2.hfix17_9_2 Q2.hinj17_9_2
      Q2.hcardT17_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_9_2 i) (Q2.hfix17_9_2 i) _)
      colCert_17_9_2.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T17_9
      hfix17_9 hinj17_9 hcardT17_9
      (fun i => conj_mem_of_fixedPoints _ _ (T17_9 i) (hfix17_9 i) _)
      ⟨17, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T17_9_2 Q2.hfix17_9_2 Q2.hinj17_9_2
      Q2.hcardT17_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_9_2 i) (Q2.hfix17_9_2 i) _)
      colCert_17_9_3.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T17_9
      hfix17_9 hinj17_9 hcardT17_9
      (fun i => conj_mem_of_fixedPoints _ _ (T17_9 i) (hfix17_9 i) _)
      ⟨17, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T17_9_2 Q2.hfix17_9_2 Q2.hinj17_9_2
      Q2.hcardT17_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_9_2 i) (Q2.hfix17_9_2 i) _)
      colCert_17_9_4.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T17_11
      hfix17_11 hinj17_11 hcardT17_11
      (fun i => conj_mem_of_fixedPoints _ _ (T17_11 i) (hfix17_11 i) _)
      ⟨17, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T17_11_2 Q2.hfix17_11_2 Q2.hinj17_11_2
      Q2.hcardT17_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_11_2 i) (Q2.hfix17_11_2 i) _)
      colCert_17_11_0.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T17_11
      hfix17_11 hinj17_11 hcardT17_11
      (fun i => conj_mem_of_fixedPoints _ _ (T17_11 i) (hfix17_11 i) _)
      ⟨17, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T17_11_2 Q2.hfix17_11_2 Q2.hinj17_11_2
      Q2.hcardT17_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_11_2 i) (Q2.hfix17_11_2 i) _)
      colCert_17_11_1.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T17_11
      hfix17_11 hinj17_11 hcardT17_11
      (fun i => conj_mem_of_fixedPoints _ _ (T17_11 i) (hfix17_11 i) _)
      ⟨17, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T17_11_2 Q2.hfix17_11_2 Q2.hinj17_11_2
      Q2.hcardT17_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_11_2 i) (Q2.hfix17_11_2 i) _)
      colCert_17_11_2.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T17_11
      hfix17_11 hinj17_11 hcardT17_11
      (fun i => conj_mem_of_fixedPoints _ _ (T17_11 i) (hfix17_11 i) _)
      ⟨17, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T17_11_2 Q2.hfix17_11_2 Q2.hinj17_11_2
      Q2.hcardT17_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_11_2 i) (Q2.hfix17_11_2 i) _)
      colCert_17_11_3.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T17_11
      hfix17_11 hinj17_11 hcardT17_11
      (fun i => conj_mem_of_fixedPoints _ _ (T17_11 i) (hfix17_11 i) _)
      ⟨17, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T17_11_2 Q2.hfix17_11_2 Q2.hinj17_11_2
      Q2.hcardT17_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_11_2 i) (Q2.hfix17_11_2 i) _)
      colCert_17_11_4.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_0 (hp : 0 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 0 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 0 (transLenTr ⟨17, by decide⟩ 0 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 0 (transLenTr ⟨17, by decide⟩ 0 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 0 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_0.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_1 (hp : 1 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 1 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 1 (transLenTr ⟨17, by decide⟩ 1 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 1 (transLenTr ⟨17, by decide⟩ 1 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 1 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_1.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_2 (hp : 2 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 2 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 2 (transLenTr ⟨17, by decide⟩ 2 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 2 (transLenTr ⟨17, by decide⟩ 2 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 2 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_2.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_3 (hp : 3 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 3 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 3 (transLenTr ⟨17, by decide⟩ 3 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 3 (transLenTr ⟨17, by decide⟩ 3 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 3 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_3.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_4 (hp : 4 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 4 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 4 (transLenTr ⟨17, by decide⟩ 4 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 4 (transLenTr ⟨17, by decide⟩ 4 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 4 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_4.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_5 (hp : 5 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 5 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 5 (transLenTr ⟨17, by decide⟩ 5 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 5 (transLenTr ⟨17, by decide⟩ 5 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 5 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_5.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_6 (hp : 6 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 6 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 6 (transLenTr ⟨17, by decide⟩ 6 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 6 (transLenTr ⟨17, by decide⟩ 6 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 6 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_6.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_7 (hp : 7 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 7 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 7 (transLenTr ⟨17, by decide⟩ 7 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 7 (transLenTr ⟨17, by decide⟩ 7 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 7 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_7.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_8 (hp : 8 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 8 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 8 (transLenTr ⟨17, by decide⟩ 8 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 8 (transLenTr ⟨17, by decide⟩ 8 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 8 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_8.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_9 (hp : 9 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 9 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 9 (transLenTr ⟨17, by decide⟩ 9 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 9 (transLenTr ⟨17, by decide⟩ 9 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 9 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_9.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_10 (hp : 10 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 10 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 10 (transLenTr ⟨17, by decide⟩ 10 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 10 (transLenTr ⟨17, by decide⟩ 10 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 10 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_10.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_11 (hp : 11 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 11 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 11 (transLenTr ⟨17, by decide⟩ 11 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 11 (transLenTr ⟨17, by decide⟩ 11 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 11 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_11.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_12 (hp : 12 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 12 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 12 (transLenTr ⟨17, by decide⟩ 12 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 12 (transLenTr ⟨17, by decide⟩ 12 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 12 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_12.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_13 (hp : 13 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 13 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 13 (transLenTr ⟨17, by decide⟩ 13 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 13 (transLenTr ⟨17, by decide⟩ 13 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 13 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_13.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_14 (hp : 14 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 14 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 14 (transLenTr ⟨17, by decide⟩ 14 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 14 (transLenTr ⟨17, by decide⟩ 14 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 14 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_14.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_15 (hp : 15 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 15 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 15 (transLenTr ⟨17, by decide⟩ 15 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 15 (transLenTr ⟨17, by decide⟩ 15 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 15 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_15.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_16 (hp : 16 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 16 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 16 (transLenTr ⟨17, by decide⟩ 16 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 16 (transLenTr ⟨17, by decide⟩ 16 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 16 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_16.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_17 (hp : 17 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 17 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 17 (transLenTr ⟨17, by decide⟩ 17 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 17 (transLenTr ⟨17, by decide⟩ 17 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 17 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_17.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_18 (hp : 18 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 18 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 18 (transLenTr ⟨17, by decide⟩ 18 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 18 (transLenTr ⟨17, by decide⟩ 18 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 18 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_18.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_19 (hp : 19 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 19 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 19 (transLenTr ⟨17, by decide⟩ 19 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 19 (transLenTr ⟨17, by decide⟩ 19 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 19 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_19.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_20 (hp : 20 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 20 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 20 (transLenTr ⟨17, by decide⟩ 20 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 20 (transLenTr ⟨17, by decide⟩ 20 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 20 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_20.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_21 (hp : 21 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 21 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 21 (transLenTr ⟨17, by decide⟩ 21 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 21 (transLenTr ⟨17, by decide⟩ 21 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 21 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_21.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_22 (hp : 22 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 22 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 22 (transLenTr ⟨17, by decide⟩ 22 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 22 (transLenTr ⟨17, by decide⟩ 22 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 22 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_22.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_23 (hp : 23 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 23 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 23 (transLenTr ⟨17, by decide⟩ 23 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 23 (transLenTr ⟨17, by decide⟩ 23 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 23 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_23.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_17_17_24 (hp : 24 < (Q2.transData.getD 17 []).length)
    (j : Nat) (hj : j < (repChars.getD 17 []).length)
    (hq : (normIsRep.getD 17 []).getD j false = true) :
    species (Q2.reps (⟨17, by decide⟩ : Fin 148)) (colE2 ⟨17, by decide⟩ 24 hp)
        (rowE2 (⟨17, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨17, by decide⟩ : Fin 148))
        (colE1 ⟨17, by decide⟩ 24 (transLenTr ⟨17, by decide⟩ 24 hp))
        (rowE1 (⟨17, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨17, by decide⟩ : Fin 148) ⟨17, by decide⟩ _
      (validAt ⟨17, by decide⟩ (listedAt ⟨17, by decide⟩ hj))
      (colE1 ⟨17, by decide⟩ 24 (transLenTr ⟨17, by decide⟩ 24 hp)) T17_17
      hfix17_17 hinj17_17 hcardT17_17
      (fun i => conj_mem_of_fixedPoints _ _ (T17_17 i) (hfix17_17 i) _)
      ⟨17, by decide⟩ ⟨17, by decide⟩ _
      (Q2.validAt ⟨17, by decide⟩ (Q2.listedAt ⟨17, by decide⟩
        (alnCheck_rep ⟨17, by decide⟩ hj hq).1))
      (colE2 ⟨17, by decide⟩ 24 hp) Q2.T17_17_2 Q2.hfix17_17_2 Q2.hinj17_17_2
      Q2.hcardT17_17_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T17_17_2 i) (Q2.hfix17_17_2 i) _)
      colCert_17_17_24.hD ?_).symm
  rw [alnId_17 j hj]


theorem leaf_18_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T18_2
      hfix18_2 hinj18_2 hcardT18_2
      (fun i => conj_mem_of_fixedPoints _ _ (T18_2 i) (hfix18_2 i) _)
      ⟨18, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T18_2_2 Q2.hfix18_2_2 Q2.hinj18_2_2
      Q2.hcardT18_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_2_2 i) (Q2.hfix18_2_2 i) _)
      colCert_18_2_0.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T18_2
      hfix18_2 hinj18_2 hcardT18_2
      (fun i => conj_mem_of_fixedPoints _ _ (T18_2 i) (hfix18_2 i) _)
      ⟨18, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T18_2_2 Q2.hfix18_2_2 Q2.hinj18_2_2
      Q2.hcardT18_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_2_2 i) (Q2.hfix18_2_2 i) _)
      colCert_18_2_1.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T18_2
      hfix18_2 hinj18_2 hcardT18_2
      (fun i => conj_mem_of_fixedPoints _ _ (T18_2 i) (hfix18_2 i) _)
      ⟨18, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T18_2_2 Q2.hfix18_2_2 Q2.hinj18_2_2
      Q2.hcardT18_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_2_2 i) (Q2.hfix18_2_2 i) _)
      colCert_18_2_2.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T18_2
      hfix18_2 hinj18_2 hcardT18_2
      (fun i => conj_mem_of_fixedPoints _ _ (T18_2 i) (hfix18_2 i) _)
      ⟨18, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T18_2_2 Q2.hfix18_2_2 Q2.hinj18_2_2
      Q2.hcardT18_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_2_2 i) (Q2.hfix18_2_2 i) _)
      colCert_18_2_3.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T18_2
      hfix18_2 hinj18_2 hcardT18_2
      (fun i => conj_mem_of_fixedPoints _ _ (T18_2 i) (hfix18_2 i) _)
      ⟨18, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T18_2_2 Q2.hfix18_2_2 Q2.hinj18_2_2
      Q2.hcardT18_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_2_2 i) (Q2.hfix18_2_2 i) _)
      colCert_18_2_4.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T18_3
      hfix18_3 hinj18_3 hcardT18_3
      (fun i => conj_mem_of_fixedPoints _ _ (T18_3 i) (hfix18_3 i) _)
      ⟨18, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T18_3_2 Q2.hfix18_3_2 Q2.hinj18_3_2
      Q2.hcardT18_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_3_2 i) (Q2.hfix18_3_2 i) _)
      colCert_18_3_0.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T18_3
      hfix18_3 hinj18_3 hcardT18_3
      (fun i => conj_mem_of_fixedPoints _ _ (T18_3 i) (hfix18_3 i) _)
      ⟨18, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T18_3_2 Q2.hfix18_3_2 Q2.hinj18_3_2
      Q2.hcardT18_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_3_2 i) (Q2.hfix18_3_2 i) _)
      colCert_18_3_1.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T18_3
      hfix18_3 hinj18_3 hcardT18_3
      (fun i => conj_mem_of_fixedPoints _ _ (T18_3 i) (hfix18_3 i) _)
      ⟨18, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T18_3_2 Q2.hfix18_3_2 Q2.hinj18_3_2
      Q2.hcardT18_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_3_2 i) (Q2.hfix18_3_2 i) _)
      colCert_18_3_2.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T18_3
      hfix18_3 hinj18_3 hcardT18_3
      (fun i => conj_mem_of_fixedPoints _ _ (T18_3 i) (hfix18_3 i) _)
      ⟨18, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T18_3_2 Q2.hfix18_3_2 Q2.hinj18_3_2
      Q2.hcardT18_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_3_2 i) (Q2.hfix18_3_2 i) _)
      colCert_18_3_3.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T18_3
      hfix18_3 hinj18_3 hcardT18_3
      (fun i => conj_mem_of_fixedPoints _ _ (T18_3 i) (hfix18_3 i) _)
      ⟨18, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T18_3_2 Q2.hfix18_3_2 Q2.hinj18_3_2
      Q2.hcardT18_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_3_2 i) (Q2.hfix18_3_2 i) _)
      colCert_18_3_4.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T18_4
      hfix18_4 hinj18_4 hcardT18_4
      (fun i => conj_mem_of_fixedPoints _ _ (T18_4 i) (hfix18_4 i) _)
      ⟨18, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T18_4_2 Q2.hfix18_4_2 Q2.hinj18_4_2
      Q2.hcardT18_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_4_2 i) (Q2.hfix18_4_2 i) _)
      colCert_18_4_0.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T18_4
      hfix18_4 hinj18_4 hcardT18_4
      (fun i => conj_mem_of_fixedPoints _ _ (T18_4 i) (hfix18_4 i) _)
      ⟨18, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T18_4_2 Q2.hfix18_4_2 Q2.hinj18_4_2
      Q2.hcardT18_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_4_2 i) (Q2.hfix18_4_2 i) _)
      colCert_18_4_1.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T18_4
      hfix18_4 hinj18_4 hcardT18_4
      (fun i => conj_mem_of_fixedPoints _ _ (T18_4 i) (hfix18_4 i) _)
      ⟨18, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T18_4_2 Q2.hfix18_4_2 Q2.hinj18_4_2
      Q2.hcardT18_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_4_2 i) (Q2.hfix18_4_2 i) _)
      colCert_18_4_2.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T18_4
      hfix18_4 hinj18_4 hcardT18_4
      (fun i => conj_mem_of_fixedPoints _ _ (T18_4 i) (hfix18_4 i) _)
      ⟨18, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T18_4_2 Q2.hfix18_4_2 Q2.hinj18_4_2
      Q2.hcardT18_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_4_2 i) (Q2.hfix18_4_2 i) _)
      colCert_18_4_3.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T18_4
      hfix18_4 hinj18_4 hcardT18_4
      (fun i => conj_mem_of_fixedPoints _ _ (T18_4 i) (hfix18_4 i) _)
      ⟨18, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T18_4_2 Q2.hfix18_4_2 Q2.hinj18_4_2
      Q2.hcardT18_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_4_2 i) (Q2.hfix18_4_2 i) _)
      colCert_18_4_4.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T18_5
      hfix18_5 hinj18_5 hcardT18_5
      (fun i => conj_mem_of_fixedPoints _ _ (T18_5 i) (hfix18_5 i) _)
      ⟨18, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T18_5_2 Q2.hfix18_5_2 Q2.hinj18_5_2
      Q2.hcardT18_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_5_2 i) (Q2.hfix18_5_2 i) _)
      colCert_18_5_0.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T18_5
      hfix18_5 hinj18_5 hcardT18_5
      (fun i => conj_mem_of_fixedPoints _ _ (T18_5 i) (hfix18_5 i) _)
      ⟨18, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T18_5_2 Q2.hfix18_5_2 Q2.hinj18_5_2
      Q2.hcardT18_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_5_2 i) (Q2.hfix18_5_2 i) _)
      colCert_18_5_1.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T18_5
      hfix18_5 hinj18_5 hcardT18_5
      (fun i => conj_mem_of_fixedPoints _ _ (T18_5 i) (hfix18_5 i) _)
      ⟨18, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T18_5_2 Q2.hfix18_5_2 Q2.hinj18_5_2
      Q2.hcardT18_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_5_2 i) (Q2.hfix18_5_2 i) _)
      colCert_18_5_2.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T18_5
      hfix18_5 hinj18_5 hcardT18_5
      (fun i => conj_mem_of_fixedPoints _ _ (T18_5 i) (hfix18_5 i) _)
      ⟨18, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T18_5_2 Q2.hfix18_5_2 Q2.hinj18_5_2
      Q2.hcardT18_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_5_2 i) (Q2.hfix18_5_2 i) _)
      colCert_18_5_3.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T18_5
      hfix18_5 hinj18_5 hcardT18_5
      (fun i => conj_mem_of_fixedPoints _ _ (T18_5 i) (hfix18_5 i) _)
      ⟨18, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T18_5_2 Q2.hfix18_5_2 Q2.hinj18_5_2
      Q2.hcardT18_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_5_2 i) (Q2.hfix18_5_2 i) _)
      colCert_18_5_4.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T18_9
      hfix18_9 hinj18_9 hcardT18_9
      (fun i => conj_mem_of_fixedPoints _ _ (T18_9 i) (hfix18_9 i) _)
      ⟨18, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T18_9_2 Q2.hfix18_9_2 Q2.hinj18_9_2
      Q2.hcardT18_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_9_2 i) (Q2.hfix18_9_2 i) _)
      colCert_18_9_0.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T18_9
      hfix18_9 hinj18_9 hcardT18_9
      (fun i => conj_mem_of_fixedPoints _ _ (T18_9 i) (hfix18_9 i) _)
      ⟨18, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T18_9_2 Q2.hfix18_9_2 Q2.hinj18_9_2
      Q2.hcardT18_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_9_2 i) (Q2.hfix18_9_2 i) _)
      colCert_18_9_1.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T18_9
      hfix18_9 hinj18_9 hcardT18_9
      (fun i => conj_mem_of_fixedPoints _ _ (T18_9 i) (hfix18_9 i) _)
      ⟨18, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T18_9_2 Q2.hfix18_9_2 Q2.hinj18_9_2
      Q2.hcardT18_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_9_2 i) (Q2.hfix18_9_2 i) _)
      colCert_18_9_2.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T18_9
      hfix18_9 hinj18_9 hcardT18_9
      (fun i => conj_mem_of_fixedPoints _ _ (T18_9 i) (hfix18_9 i) _)
      ⟨18, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T18_9_2 Q2.hfix18_9_2 Q2.hinj18_9_2
      Q2.hcardT18_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_9_2 i) (Q2.hfix18_9_2 i) _)
      colCert_18_9_3.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T18_9
      hfix18_9 hinj18_9 hcardT18_9
      (fun i => conj_mem_of_fixedPoints _ _ (T18_9 i) (hfix18_9 i) _)
      ⟨18, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T18_9_2 Q2.hfix18_9_2 Q2.hinj18_9_2
      Q2.hcardT18_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_9_2 i) (Q2.hfix18_9_2 i) _)
      colCert_18_9_4.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_11_0 (hp : 0 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 0 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 0 (transLenTr ⟨11, by decide⟩ 0 hp)) T18_11
      hfix18_11 hinj18_11 hcardT18_11
      (fun i => conj_mem_of_fixedPoints _ _ (T18_11 i) (hfix18_11 i) _)
      ⟨18, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 0 hp) Q2.T18_11_2 Q2.hfix18_11_2 Q2.hinj18_11_2
      Q2.hcardT18_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_11_2 i) (Q2.hfix18_11_2 i) _)
      colCert_18_11_0.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_11_1 (hp : 1 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 1 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 1 (transLenTr ⟨11, by decide⟩ 1 hp)) T18_11
      hfix18_11 hinj18_11 hcardT18_11
      (fun i => conj_mem_of_fixedPoints _ _ (T18_11 i) (hfix18_11 i) _)
      ⟨18, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 1 hp) Q2.T18_11_2 Q2.hfix18_11_2 Q2.hinj18_11_2
      Q2.hcardT18_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_11_2 i) (Q2.hfix18_11_2 i) _)
      colCert_18_11_1.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_11_2 (hp : 2 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 2 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 2 (transLenTr ⟨11, by decide⟩ 2 hp)) T18_11
      hfix18_11 hinj18_11 hcardT18_11
      (fun i => conj_mem_of_fixedPoints _ _ (T18_11 i) (hfix18_11 i) _)
      ⟨18, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 2 hp) Q2.T18_11_2 Q2.hfix18_11_2 Q2.hinj18_11_2
      Q2.hcardT18_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_11_2 i) (Q2.hfix18_11_2 i) _)
      colCert_18_11_2.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_11_3 (hp : 3 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 3 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 3 (transLenTr ⟨11, by decide⟩ 3 hp)) T18_11
      hfix18_11 hinj18_11 hcardT18_11
      (fun i => conj_mem_of_fixedPoints _ _ (T18_11 i) (hfix18_11 i) _)
      ⟨18, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 3 hp) Q2.T18_11_2 Q2.hfix18_11_2 Q2.hinj18_11_2
      Q2.hcardT18_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_11_2 i) (Q2.hfix18_11_2 i) _)
      colCert_18_11_3.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_11_4 (hp : 4 < (Q2.transData.getD 11 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨11, by decide⟩ : Fin 148)) (colE2 ⟨11, by decide⟩ 4 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨11, by decide⟩ : Fin 148))
        (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨11, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨11, by decide⟩ 4 (transLenTr ⟨11, by decide⟩ 4 hp)) T18_11
      hfix18_11 hinj18_11 hcardT18_11
      (fun i => conj_mem_of_fixedPoints _ _ (T18_11 i) (hfix18_11 i) _)
      ⟨18, by decide⟩ ⟨11, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨11, by decide⟩ 4 hp) Q2.T18_11_2 Q2.hfix18_11_2 Q2.hinj18_11_2
      Q2.hcardT18_11_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_11_2 i) (Q2.hfix18_11_2 i) _)
      colCert_18_11_4.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_0 (hp : 0 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 0 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 0 (transLenTr ⟨18, by decide⟩ 0 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 0 (transLenTr ⟨18, by decide⟩ 0 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 0 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_0.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_1 (hp : 1 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 1 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 1 (transLenTr ⟨18, by decide⟩ 1 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 1 (transLenTr ⟨18, by decide⟩ 1 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 1 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_1.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_2 (hp : 2 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 2 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 2 (transLenTr ⟨18, by decide⟩ 2 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 2 (transLenTr ⟨18, by decide⟩ 2 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 2 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_2.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_3 (hp : 3 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 3 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 3 (transLenTr ⟨18, by decide⟩ 3 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 3 (transLenTr ⟨18, by decide⟩ 3 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 3 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_3.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_4 (hp : 4 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 4 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 4 (transLenTr ⟨18, by decide⟩ 4 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 4 (transLenTr ⟨18, by decide⟩ 4 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 4 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_4.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_5 (hp : 5 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 5 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 5 (transLenTr ⟨18, by decide⟩ 5 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 5 (transLenTr ⟨18, by decide⟩ 5 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 5 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_5.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_6 (hp : 6 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 6 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 6 (transLenTr ⟨18, by decide⟩ 6 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 6 (transLenTr ⟨18, by decide⟩ 6 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 6 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_6.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_7 (hp : 7 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 7 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 7 (transLenTr ⟨18, by decide⟩ 7 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 7 (transLenTr ⟨18, by decide⟩ 7 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 7 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_7.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_8 (hp : 8 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 8 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 8 (transLenTr ⟨18, by decide⟩ 8 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 8 (transLenTr ⟨18, by decide⟩ 8 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 8 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_8.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_9 (hp : 9 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 9 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 9 (transLenTr ⟨18, by decide⟩ 9 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 9 (transLenTr ⟨18, by decide⟩ 9 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 9 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_9.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_10 (hp : 10 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 10 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 10 (transLenTr ⟨18, by decide⟩ 10 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 10 (transLenTr ⟨18, by decide⟩ 10 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 10 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_10.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_11 (hp : 11 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 11 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 11 (transLenTr ⟨18, by decide⟩ 11 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 11 (transLenTr ⟨18, by decide⟩ 11 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 11 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_11.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_12 (hp : 12 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 12 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 12 (transLenTr ⟨18, by decide⟩ 12 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 12 (transLenTr ⟨18, by decide⟩ 12 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 12 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_12.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_13 (hp : 13 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 13 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 13 (transLenTr ⟨18, by decide⟩ 13 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 13 (transLenTr ⟨18, by decide⟩ 13 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 13 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_13.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_14 (hp : 14 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 14 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 14 (transLenTr ⟨18, by decide⟩ 14 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 14 (transLenTr ⟨18, by decide⟩ 14 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 14 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_14.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_15 (hp : 15 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 15 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 15 (transLenTr ⟨18, by decide⟩ 15 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 15 (transLenTr ⟨18, by decide⟩ 15 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 15 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_15.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_16 (hp : 16 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 16 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 16 (transLenTr ⟨18, by decide⟩ 16 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 16 (transLenTr ⟨18, by decide⟩ 16 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 16 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_16.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_17 (hp : 17 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 17 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 17 (transLenTr ⟨18, by decide⟩ 17 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 17 (transLenTr ⟨18, by decide⟩ 17 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 17 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_17.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_18 (hp : 18 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 18 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 18 (transLenTr ⟨18, by decide⟩ 18 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 18 (transLenTr ⟨18, by decide⟩ 18 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 18 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_18.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_19 (hp : 19 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 19 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 19 (transLenTr ⟨18, by decide⟩ 19 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 19 (transLenTr ⟨18, by decide⟩ 19 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 19 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_19.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_20 (hp : 20 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 20 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 20 (transLenTr ⟨18, by decide⟩ 20 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 20 (transLenTr ⟨18, by decide⟩ 20 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 20 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_20.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_21 (hp : 21 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 21 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 21 (transLenTr ⟨18, by decide⟩ 21 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 21 (transLenTr ⟨18, by decide⟩ 21 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 21 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_21.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_22 (hp : 22 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 22 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 22 (transLenTr ⟨18, by decide⟩ 22 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 22 (transLenTr ⟨18, by decide⟩ 22 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 22 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_22.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_23 (hp : 23 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 23 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 23 (transLenTr ⟨18, by decide⟩ 23 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 23 (transLenTr ⟨18, by decide⟩ 23 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 23 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_23.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_18_18_24 (hp : 24 < (Q2.transData.getD 18 []).length)
    (j : Nat) (hj : j < (repChars.getD 18 []).length)
    (hq : (normIsRep.getD 18 []).getD j false = true) :
    species (Q2.reps (⟨18, by decide⟩ : Fin 148)) (colE2 ⟨18, by decide⟩ 24 hp)
        (rowE2 (⟨18, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨18, by decide⟩ : Fin 148))
        (colE1 ⟨18, by decide⟩ 24 (transLenTr ⟨18, by decide⟩ 24 hp))
        (rowE1 (⟨18, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨18, by decide⟩ : Fin 148) ⟨18, by decide⟩ _
      (validAt ⟨18, by decide⟩ (listedAt ⟨18, by decide⟩ hj))
      (colE1 ⟨18, by decide⟩ 24 (transLenTr ⟨18, by decide⟩ 24 hp)) T18_18
      hfix18_18 hinj18_18 hcardT18_18
      (fun i => conj_mem_of_fixedPoints _ _ (T18_18 i) (hfix18_18 i) _)
      ⟨18, by decide⟩ ⟨18, by decide⟩ _
      (Q2.validAt ⟨18, by decide⟩ (Q2.listedAt ⟨18, by decide⟩
        (alnCheck_rep ⟨18, by decide⟩ hj hq).1))
      (colE2 ⟨18, by decide⟩ 24 hp) Q2.T18_18_2 Q2.hfix18_18_2 Q2.hinj18_18_2
      Q2.hcardT18_18_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T18_18_2 i) (Q2.hfix18_18_2 i) _)
      colCert_18_18_24.hD ?_).symm
  rw [alnId_18 j hj]


theorem leaf_19_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T19_1
      hfix19_1 hinj19_1 hcardT19_1
      (fun i => conj_mem_of_fixedPoints _ _ (T19_1 i) (hfix19_1 i) _)
      ⟨19, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T19_1_2 Q2.hfix19_1_2 Q2.hinj19_1_2
      Q2.hcardT19_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_1_2 i) (Q2.hfix19_1_2 i) _)
      colCert_19_1_0.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T19_1
      hfix19_1 hinj19_1 hcardT19_1
      (fun i => conj_mem_of_fixedPoints _ _ (T19_1 i) (hfix19_1 i) _)
      ⟨19, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T19_1_2 Q2.hfix19_1_2 Q2.hinj19_1_2
      Q2.hcardT19_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_1_2 i) (Q2.hfix19_1_2 i) _)
      colCert_19_1_1.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T19_1
      hfix19_1 hinj19_1 hcardT19_1
      (fun i => conj_mem_of_fixedPoints _ _ (T19_1 i) (hfix19_1 i) _)
      ⟨19, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T19_1_2 Q2.hfix19_1_2 Q2.hinj19_1_2
      Q2.hcardT19_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_1_2 i) (Q2.hfix19_1_2 i) _)
      colCert_19_1_2.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T19_1
      hfix19_1 hinj19_1 hcardT19_1
      (fun i => conj_mem_of_fixedPoints _ _ (T19_1 i) (hfix19_1 i) _)
      ⟨19, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T19_1_2 Q2.hfix19_1_2 Q2.hinj19_1_2
      Q2.hcardT19_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_1_2 i) (Q2.hfix19_1_2 i) _)
      colCert_19_1_3.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T19_1
      hfix19_1 hinj19_1 hcardT19_1
      (fun i => conj_mem_of_fixedPoints _ _ (T19_1 i) (hfix19_1 i) _)
      ⟨19, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T19_1_2 Q2.hfix19_1_2 Q2.hinj19_1_2
      Q2.hcardT19_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_1_2 i) (Q2.hfix19_1_2 i) _)
      colCert_19_1_4.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T19_12
      hfix19_12 hinj19_12 hcardT19_12
      (fun i => conj_mem_of_fixedPoints _ _ (T19_12 i) (hfix19_12 i) _)
      ⟨19, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T19_12_2 Q2.hfix19_12_2 Q2.hinj19_12_2
      Q2.hcardT19_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_12_2 i) (Q2.hfix19_12_2 i) _)
      colCert_19_12_0.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T19_12
      hfix19_12 hinj19_12 hcardT19_12
      (fun i => conj_mem_of_fixedPoints _ _ (T19_12 i) (hfix19_12 i) _)
      ⟨19, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T19_12_2 Q2.hfix19_12_2 Q2.hinj19_12_2
      Q2.hcardT19_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_12_2 i) (Q2.hfix19_12_2 i) _)
      colCert_19_12_1.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T19_12
      hfix19_12 hinj19_12 hcardT19_12
      (fun i => conj_mem_of_fixedPoints _ _ (T19_12 i) (hfix19_12 i) _)
      ⟨19, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T19_12_2 Q2.hfix19_12_2 Q2.hinj19_12_2
      Q2.hcardT19_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_12_2 i) (Q2.hfix19_12_2 i) _)
      colCert_19_12_2.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T19_12
      hfix19_12 hinj19_12 hcardT19_12
      (fun i => conj_mem_of_fixedPoints _ _ (T19_12 i) (hfix19_12 i) _)
      ⟨19, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T19_12_2 Q2.hfix19_12_2 Q2.hinj19_12_2
      Q2.hcardT19_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_12_2 i) (Q2.hfix19_12_2 i) _)
      colCert_19_12_3.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T19_12
      hfix19_12 hinj19_12 hcardT19_12
      (fun i => conj_mem_of_fixedPoints _ _ (T19_12 i) (hfix19_12 i) _)
      ⟨19, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T19_12_2 Q2.hfix19_12_2 Q2.hinj19_12_2
      Q2.hcardT19_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_12_2 i) (Q2.hfix19_12_2 i) _)
      colCert_19_12_4.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T19_19
      hfix19_19 hinj19_19 hcardT19_19
      (fun i => conj_mem_of_fixedPoints _ _ (T19_19 i) (hfix19_19 i) _)
      ⟨19, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T19_19_2 Q2.hfix19_19_2 Q2.hinj19_19_2
      Q2.hcardT19_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_19_2 i) (Q2.hfix19_19_2 i) _)
      colCert_19_19_0.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T19_19
      hfix19_19 hinj19_19 hcardT19_19
      (fun i => conj_mem_of_fixedPoints _ _ (T19_19 i) (hfix19_19 i) _)
      ⟨19, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T19_19_2 Q2.hfix19_19_2 Q2.hinj19_19_2
      Q2.hcardT19_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_19_2 i) (Q2.hfix19_19_2 i) _)
      colCert_19_19_1.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T19_19
      hfix19_19 hinj19_19 hcardT19_19
      (fun i => conj_mem_of_fixedPoints _ _ (T19_19 i) (hfix19_19 i) _)
      ⟨19, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T19_19_2 Q2.hfix19_19_2 Q2.hinj19_19_2
      Q2.hcardT19_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_19_2 i) (Q2.hfix19_19_2 i) _)
      colCert_19_19_2.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T19_19
      hfix19_19 hinj19_19 hcardT19_19
      (fun i => conj_mem_of_fixedPoints _ _ (T19_19 i) (hfix19_19 i) _)
      ⟨19, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T19_19_2 Q2.hfix19_19_2 Q2.hinj19_19_2
      Q2.hcardT19_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_19_2 i) (Q2.hfix19_19_2 i) _)
      colCert_19_19_3.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T19_19
      hfix19_19 hinj19_19 hcardT19_19
      (fun i => conj_mem_of_fixedPoints _ _ (T19_19 i) (hfix19_19 i) _)
      ⟨19, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T19_19_2 Q2.hfix19_19_2 Q2.hinj19_19_2
      Q2.hcardT19_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_19_2 i) (Q2.hfix19_19_2 i) _)
      colCert_19_19_4.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T19_19
      hfix19_19 hinj19_19 hcardT19_19
      (fun i => conj_mem_of_fixedPoints _ _ (T19_19 i) (hfix19_19 i) _)
      ⟨19, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T19_19_2 Q2.hfix19_19_2 Q2.hinj19_19_2
      Q2.hcardT19_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_19_2 i) (Q2.hfix19_19_2 i) _)
      colCert_19_19_5.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T19_19
      hfix19_19 hinj19_19 hcardT19_19
      (fun i => conj_mem_of_fixedPoints _ _ (T19_19 i) (hfix19_19 i) _)
      ⟨19, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T19_19_2 Q2.hfix19_19_2 Q2.hinj19_19_2
      Q2.hcardT19_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_19_2 i) (Q2.hfix19_19_2 i) _)
      colCert_19_19_10.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T19_19
      hfix19_19 hinj19_19 hcardT19_19
      (fun i => conj_mem_of_fixedPoints _ _ (T19_19 i) (hfix19_19 i) _)
      ⟨19, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T19_19_2 Q2.hfix19_19_2 Q2.hinj19_19_2
      Q2.hcardT19_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_19_2 i) (Q2.hfix19_19_2 i) _)
      colCert_19_19_15.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_19_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 19 []).length)
    (hq : (normIsRep.getD 19 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨19, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨19, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨19, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨19, by decide⟩ (listedAt ⟨19, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T19_19
      hfix19_19 hinj19_19 hcardT19_19
      (fun i => conj_mem_of_fixedPoints _ _ (T19_19 i) (hfix19_19 i) _)
      ⟨19, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨19, by decide⟩ (Q2.listedAt ⟨19, by decide⟩
        (alnCheck_rep ⟨19, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T19_19_2 Q2.hfix19_19_2 Q2.hinj19_19_2
      Q2.hcardT19_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T19_19_2 i) (Q2.hfix19_19_2 i) _)
      colCert_19_19_20.hD ?_).symm
  rw [alnId_19 j hj]


theorem leaf_20_2_0 (hp : 0 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 0 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 0 (transLenTr ⟨2, by decide⟩ 0 hp)) T20_2
      hfix20_2 hinj20_2 hcardT20_2
      (fun i => conj_mem_of_fixedPoints _ _ (T20_2 i) (hfix20_2 i) _)
      ⟨20, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 0 hp) Q2.T20_2_2 Q2.hfix20_2_2 Q2.hinj20_2_2
      Q2.hcardT20_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_2_2 i) (Q2.hfix20_2_2 i) _)
      colCert_20_2_0.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_2_1 (hp : 1 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 1 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 1 (transLenTr ⟨2, by decide⟩ 1 hp)) T20_2
      hfix20_2 hinj20_2 hcardT20_2
      (fun i => conj_mem_of_fixedPoints _ _ (T20_2 i) (hfix20_2 i) _)
      ⟨20, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 1 hp) Q2.T20_2_2 Q2.hfix20_2_2 Q2.hinj20_2_2
      Q2.hcardT20_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_2_2 i) (Q2.hfix20_2_2 i) _)
      colCert_20_2_1.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_2_2 (hp : 2 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 2 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 2 (transLenTr ⟨2, by decide⟩ 2 hp)) T20_2
      hfix20_2 hinj20_2 hcardT20_2
      (fun i => conj_mem_of_fixedPoints _ _ (T20_2 i) (hfix20_2 i) _)
      ⟨20, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 2 hp) Q2.T20_2_2 Q2.hfix20_2_2 Q2.hinj20_2_2
      Q2.hcardT20_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_2_2 i) (Q2.hfix20_2_2 i) _)
      colCert_20_2_2.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_2_3 (hp : 3 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 3 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 3 (transLenTr ⟨2, by decide⟩ 3 hp)) T20_2
      hfix20_2 hinj20_2 hcardT20_2
      (fun i => conj_mem_of_fixedPoints _ _ (T20_2 i) (hfix20_2 i) _)
      ⟨20, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 3 hp) Q2.T20_2_2 Q2.hfix20_2_2 Q2.hinj20_2_2
      Q2.hcardT20_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_2_2 i) (Q2.hfix20_2_2 i) _)
      colCert_20_2_3.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_2_4 (hp : 4 < (Q2.transData.getD 2 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨2, by decide⟩ : Fin 148)) (colE2 ⟨2, by decide⟩ 4 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨2, by decide⟩ : Fin 148))
        (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨2, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨2, by decide⟩ 4 (transLenTr ⟨2, by decide⟩ 4 hp)) T20_2
      hfix20_2 hinj20_2 hcardT20_2
      (fun i => conj_mem_of_fixedPoints _ _ (T20_2 i) (hfix20_2 i) _)
      ⟨20, by decide⟩ ⟨2, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨2, by decide⟩ 4 hp) Q2.T20_2_2 Q2.hfix20_2_2 Q2.hinj20_2_2
      Q2.hcardT20_2_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_2_2 i) (Q2.hfix20_2_2 i) _)
      colCert_20_2_4.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T20_12
      hfix20_12 hinj20_12 hcardT20_12
      (fun i => conj_mem_of_fixedPoints _ _ (T20_12 i) (hfix20_12 i) _)
      ⟨20, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T20_12_2 Q2.hfix20_12_2 Q2.hinj20_12_2
      Q2.hcardT20_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_12_2 i) (Q2.hfix20_12_2 i) _)
      colCert_20_12_0.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T20_12
      hfix20_12 hinj20_12 hcardT20_12
      (fun i => conj_mem_of_fixedPoints _ _ (T20_12 i) (hfix20_12 i) _)
      ⟨20, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T20_12_2 Q2.hfix20_12_2 Q2.hinj20_12_2
      Q2.hcardT20_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_12_2 i) (Q2.hfix20_12_2 i) _)
      colCert_20_12_1.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T20_12
      hfix20_12 hinj20_12 hcardT20_12
      (fun i => conj_mem_of_fixedPoints _ _ (T20_12 i) (hfix20_12 i) _)
      ⟨20, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T20_12_2 Q2.hfix20_12_2 Q2.hinj20_12_2
      Q2.hcardT20_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_12_2 i) (Q2.hfix20_12_2 i) _)
      colCert_20_12_2.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T20_12
      hfix20_12 hinj20_12 hcardT20_12
      (fun i => conj_mem_of_fixedPoints _ _ (T20_12 i) (hfix20_12 i) _)
      ⟨20, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T20_12_2 Q2.hfix20_12_2 Q2.hinj20_12_2
      Q2.hcardT20_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_12_2 i) (Q2.hfix20_12_2 i) _)
      colCert_20_12_3.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T20_12
      hfix20_12 hinj20_12 hcardT20_12
      (fun i => conj_mem_of_fixedPoints _ _ (T20_12 i) (hfix20_12 i) _)
      ⟨20, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T20_12_2 Q2.hfix20_12_2 Q2.hinj20_12_2
      Q2.hcardT20_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_12_2 i) (Q2.hfix20_12_2 i) _)
      colCert_20_12_4.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_20_0 (hp : 0 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 0 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 0 (transLenTr ⟨20, by decide⟩ 0 hp)) T20_20
      hfix20_20 hinj20_20 hcardT20_20
      (fun i => conj_mem_of_fixedPoints _ _ (T20_20 i) (hfix20_20 i) _)
      ⟨20, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 0 hp) Q2.T20_20_2 Q2.hfix20_20_2 Q2.hinj20_20_2
      Q2.hcardT20_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_20_2 i) (Q2.hfix20_20_2 i) _)
      colCert_20_20_0.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_20_1 (hp : 1 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 1 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 1 (transLenTr ⟨20, by decide⟩ 1 hp)) T20_20
      hfix20_20 hinj20_20 hcardT20_20
      (fun i => conj_mem_of_fixedPoints _ _ (T20_20 i) (hfix20_20 i) _)
      ⟨20, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 1 hp) Q2.T20_20_2 Q2.hfix20_20_2 Q2.hinj20_20_2
      Q2.hcardT20_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_20_2 i) (Q2.hfix20_20_2 i) _)
      colCert_20_20_1.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_20_2 (hp : 2 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 2 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 2 (transLenTr ⟨20, by decide⟩ 2 hp)) T20_20
      hfix20_20 hinj20_20 hcardT20_20
      (fun i => conj_mem_of_fixedPoints _ _ (T20_20 i) (hfix20_20 i) _)
      ⟨20, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 2 hp) Q2.T20_20_2 Q2.hfix20_20_2 Q2.hinj20_20_2
      Q2.hcardT20_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_20_2 i) (Q2.hfix20_20_2 i) _)
      colCert_20_20_2.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_20_3 (hp : 3 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 3 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 3 (transLenTr ⟨20, by decide⟩ 3 hp)) T20_20
      hfix20_20 hinj20_20 hcardT20_20
      (fun i => conj_mem_of_fixedPoints _ _ (T20_20 i) (hfix20_20 i) _)
      ⟨20, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 3 hp) Q2.T20_20_2 Q2.hfix20_20_2 Q2.hinj20_20_2
      Q2.hcardT20_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_20_2 i) (Q2.hfix20_20_2 i) _)
      colCert_20_20_3.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_20_4 (hp : 4 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 4 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 4 (transLenTr ⟨20, by decide⟩ 4 hp)) T20_20
      hfix20_20 hinj20_20 hcardT20_20
      (fun i => conj_mem_of_fixedPoints _ _ (T20_20 i) (hfix20_20 i) _)
      ⟨20, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 4 hp) Q2.T20_20_2 Q2.hfix20_20_2 Q2.hinj20_20_2
      Q2.hcardT20_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_20_2 i) (Q2.hfix20_20_2 i) _)
      colCert_20_20_4.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_20_5 (hp : 5 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 5 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 5 (transLenTr ⟨20, by decide⟩ 5 hp)) T20_20
      hfix20_20 hinj20_20 hcardT20_20
      (fun i => conj_mem_of_fixedPoints _ _ (T20_20 i) (hfix20_20 i) _)
      ⟨20, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 5 hp) Q2.T20_20_2 Q2.hfix20_20_2 Q2.hinj20_20_2
      Q2.hcardT20_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_20_2 i) (Q2.hfix20_20_2 i) _)
      colCert_20_20_5.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_20_10 (hp : 10 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 10 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 10 (transLenTr ⟨20, by decide⟩ 10 hp)) T20_20
      hfix20_20 hinj20_20 hcardT20_20
      (fun i => conj_mem_of_fixedPoints _ _ (T20_20 i) (hfix20_20 i) _)
      ⟨20, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 10 hp) Q2.T20_20_2 Q2.hfix20_20_2 Q2.hinj20_20_2
      Q2.hcardT20_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_20_2 i) (Q2.hfix20_20_2 i) _)
      colCert_20_20_10.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_20_15 (hp : 15 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 15 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 15 (transLenTr ⟨20, by decide⟩ 15 hp)) T20_20
      hfix20_20 hinj20_20 hcardT20_20
      (fun i => conj_mem_of_fixedPoints _ _ (T20_20 i) (hfix20_20 i) _)
      ⟨20, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 15 hp) Q2.T20_20_2 Q2.hfix20_20_2 Q2.hinj20_20_2
      Q2.hcardT20_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_20_2 i) (Q2.hfix20_20_2 i) _)
      colCert_20_20_15.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_20_20_20 (hp : 20 < (Q2.transData.getD 20 []).length)
    (j : Nat) (hj : j < (repChars.getD 20 []).length)
    (hq : (normIsRep.getD 20 []).getD j false = true) :
    species (Q2.reps (⟨20, by decide⟩ : Fin 148)) (colE2 ⟨20, by decide⟩ 20 hp)
        (rowE2 (⟨20, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨20, by decide⟩ : Fin 148))
        (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp))
        (rowE1 (⟨20, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨20, by decide⟩ : Fin 148) ⟨20, by decide⟩ _
      (validAt ⟨20, by decide⟩ (listedAt ⟨20, by decide⟩ hj))
      (colE1 ⟨20, by decide⟩ 20 (transLenTr ⟨20, by decide⟩ 20 hp)) T20_20
      hfix20_20 hinj20_20 hcardT20_20
      (fun i => conj_mem_of_fixedPoints _ _ (T20_20 i) (hfix20_20 i) _)
      ⟨20, by decide⟩ ⟨20, by decide⟩ _
      (Q2.validAt ⟨20, by decide⟩ (Q2.listedAt ⟨20, by decide⟩
        (alnCheck_rep ⟨20, by decide⟩ hj hq).1))
      (colE2 ⟨20, by decide⟩ 20 hp) Q2.T20_20_2 Q2.hfix20_20_2 Q2.hinj20_20_2
      Q2.hcardT20_20_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T20_20_2 i) (Q2.hfix20_20_2 i) _)
      colCert_20_20_20.hD ?_).symm
  rw [alnId_20 j hj]


theorem leaf_21_3_0 (hp : 0 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 0 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 0 (transLenTr ⟨3, by decide⟩ 0 hp)) T21_3
      hfix21_3 hinj21_3 hcardT21_3
      (fun i => conj_mem_of_fixedPoints _ _ (T21_3 i) (hfix21_3 i) _)
      ⟨21, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 0 hp) Q2.T21_3_2 Q2.hfix21_3_2 Q2.hinj21_3_2
      Q2.hcardT21_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_3_2 i) (Q2.hfix21_3_2 i) _)
      colCert_21_3_0.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_3_1 (hp : 1 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 1 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 1 (transLenTr ⟨3, by decide⟩ 1 hp)) T21_3
      hfix21_3 hinj21_3 hcardT21_3
      (fun i => conj_mem_of_fixedPoints _ _ (T21_3 i) (hfix21_3 i) _)
      ⟨21, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 1 hp) Q2.T21_3_2 Q2.hfix21_3_2 Q2.hinj21_3_2
      Q2.hcardT21_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_3_2 i) (Q2.hfix21_3_2 i) _)
      colCert_21_3_1.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_3_2 (hp : 2 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 2 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 2 (transLenTr ⟨3, by decide⟩ 2 hp)) T21_3
      hfix21_3 hinj21_3 hcardT21_3
      (fun i => conj_mem_of_fixedPoints _ _ (T21_3 i) (hfix21_3 i) _)
      ⟨21, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 2 hp) Q2.T21_3_2 Q2.hfix21_3_2 Q2.hinj21_3_2
      Q2.hcardT21_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_3_2 i) (Q2.hfix21_3_2 i) _)
      colCert_21_3_2.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_3_3 (hp : 3 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 3 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 3 (transLenTr ⟨3, by decide⟩ 3 hp)) T21_3
      hfix21_3 hinj21_3 hcardT21_3
      (fun i => conj_mem_of_fixedPoints _ _ (T21_3 i) (hfix21_3 i) _)
      ⟨21, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 3 hp) Q2.T21_3_2 Q2.hfix21_3_2 Q2.hinj21_3_2
      Q2.hcardT21_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_3_2 i) (Q2.hfix21_3_2 i) _)
      colCert_21_3_3.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_3_4 (hp : 4 < (Q2.transData.getD 3 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨3, by decide⟩ : Fin 148)) (colE2 ⟨3, by decide⟩ 4 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨3, by decide⟩ : Fin 148))
        (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨3, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨3, by decide⟩ 4 (transLenTr ⟨3, by decide⟩ 4 hp)) T21_3
      hfix21_3 hinj21_3 hcardT21_3
      (fun i => conj_mem_of_fixedPoints _ _ (T21_3 i) (hfix21_3 i) _)
      ⟨21, by decide⟩ ⟨3, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨3, by decide⟩ 4 hp) Q2.T21_3_2 Q2.hfix21_3_2 Q2.hinj21_3_2
      Q2.hcardT21_3_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_3_2 i) (Q2.hfix21_3_2 i) _)
      colCert_21_3_4.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T21_12
      hfix21_12 hinj21_12 hcardT21_12
      (fun i => conj_mem_of_fixedPoints _ _ (T21_12 i) (hfix21_12 i) _)
      ⟨21, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T21_12_2 Q2.hfix21_12_2 Q2.hinj21_12_2
      Q2.hcardT21_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_12_2 i) (Q2.hfix21_12_2 i) _)
      colCert_21_12_0.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T21_12
      hfix21_12 hinj21_12 hcardT21_12
      (fun i => conj_mem_of_fixedPoints _ _ (T21_12 i) (hfix21_12 i) _)
      ⟨21, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T21_12_2 Q2.hfix21_12_2 Q2.hinj21_12_2
      Q2.hcardT21_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_12_2 i) (Q2.hfix21_12_2 i) _)
      colCert_21_12_1.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T21_12
      hfix21_12 hinj21_12 hcardT21_12
      (fun i => conj_mem_of_fixedPoints _ _ (T21_12 i) (hfix21_12 i) _)
      ⟨21, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T21_12_2 Q2.hfix21_12_2 Q2.hinj21_12_2
      Q2.hcardT21_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_12_2 i) (Q2.hfix21_12_2 i) _)
      colCert_21_12_2.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T21_12
      hfix21_12 hinj21_12 hcardT21_12
      (fun i => conj_mem_of_fixedPoints _ _ (T21_12 i) (hfix21_12 i) _)
      ⟨21, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T21_12_2 Q2.hfix21_12_2 Q2.hinj21_12_2
      Q2.hcardT21_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_12_2 i) (Q2.hfix21_12_2 i) _)
      colCert_21_12_3.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T21_12
      hfix21_12 hinj21_12 hcardT21_12
      (fun i => conj_mem_of_fixedPoints _ _ (T21_12 i) (hfix21_12 i) _)
      ⟨21, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T21_12_2 Q2.hfix21_12_2 Q2.hinj21_12_2
      Q2.hcardT21_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_12_2 i) (Q2.hfix21_12_2 i) _)
      colCert_21_12_4.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_21_0 (hp : 0 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 0 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 0 (transLenTr ⟨21, by decide⟩ 0 hp)) T21_21
      hfix21_21 hinj21_21 hcardT21_21
      (fun i => conj_mem_of_fixedPoints _ _ (T21_21 i) (hfix21_21 i) _)
      ⟨21, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 0 hp) Q2.T21_21_2 Q2.hfix21_21_2 Q2.hinj21_21_2
      Q2.hcardT21_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_21_2 i) (Q2.hfix21_21_2 i) _)
      colCert_21_21_0.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_21_1 (hp : 1 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 1 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 1 (transLenTr ⟨21, by decide⟩ 1 hp)) T21_21
      hfix21_21 hinj21_21 hcardT21_21
      (fun i => conj_mem_of_fixedPoints _ _ (T21_21 i) (hfix21_21 i) _)
      ⟨21, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 1 hp) Q2.T21_21_2 Q2.hfix21_21_2 Q2.hinj21_21_2
      Q2.hcardT21_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_21_2 i) (Q2.hfix21_21_2 i) _)
      colCert_21_21_1.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_21_2 (hp : 2 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 2 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 2 (transLenTr ⟨21, by decide⟩ 2 hp)) T21_21
      hfix21_21 hinj21_21 hcardT21_21
      (fun i => conj_mem_of_fixedPoints _ _ (T21_21 i) (hfix21_21 i) _)
      ⟨21, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 2 hp) Q2.T21_21_2 Q2.hfix21_21_2 Q2.hinj21_21_2
      Q2.hcardT21_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_21_2 i) (Q2.hfix21_21_2 i) _)
      colCert_21_21_2.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_21_3 (hp : 3 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 3 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 3 (transLenTr ⟨21, by decide⟩ 3 hp)) T21_21
      hfix21_21 hinj21_21 hcardT21_21
      (fun i => conj_mem_of_fixedPoints _ _ (T21_21 i) (hfix21_21 i) _)
      ⟨21, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 3 hp) Q2.T21_21_2 Q2.hfix21_21_2 Q2.hinj21_21_2
      Q2.hcardT21_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_21_2 i) (Q2.hfix21_21_2 i) _)
      colCert_21_21_3.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_21_4 (hp : 4 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 4 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 4 (transLenTr ⟨21, by decide⟩ 4 hp)) T21_21
      hfix21_21 hinj21_21 hcardT21_21
      (fun i => conj_mem_of_fixedPoints _ _ (T21_21 i) (hfix21_21 i) _)
      ⟨21, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 4 hp) Q2.T21_21_2 Q2.hfix21_21_2 Q2.hinj21_21_2
      Q2.hcardT21_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_21_2 i) (Q2.hfix21_21_2 i) _)
      colCert_21_21_4.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_21_5 (hp : 5 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 5 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 5 (transLenTr ⟨21, by decide⟩ 5 hp)) T21_21
      hfix21_21 hinj21_21 hcardT21_21
      (fun i => conj_mem_of_fixedPoints _ _ (T21_21 i) (hfix21_21 i) _)
      ⟨21, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 5 hp) Q2.T21_21_2 Q2.hfix21_21_2 Q2.hinj21_21_2
      Q2.hcardT21_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_21_2 i) (Q2.hfix21_21_2 i) _)
      colCert_21_21_5.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_21_10 (hp : 10 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 10 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 10 (transLenTr ⟨21, by decide⟩ 10 hp)) T21_21
      hfix21_21 hinj21_21 hcardT21_21
      (fun i => conj_mem_of_fixedPoints _ _ (T21_21 i) (hfix21_21 i) _)
      ⟨21, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 10 hp) Q2.T21_21_2 Q2.hfix21_21_2 Q2.hinj21_21_2
      Q2.hcardT21_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_21_2 i) (Q2.hfix21_21_2 i) _)
      colCert_21_21_10.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_21_15 (hp : 15 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 15 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 15 (transLenTr ⟨21, by decide⟩ 15 hp)) T21_21
      hfix21_21 hinj21_21 hcardT21_21
      (fun i => conj_mem_of_fixedPoints _ _ (T21_21 i) (hfix21_21 i) _)
      ⟨21, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 15 hp) Q2.T21_21_2 Q2.hfix21_21_2 Q2.hinj21_21_2
      Q2.hcardT21_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_21_2 i) (Q2.hfix21_21_2 i) _)
      colCert_21_21_15.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_21_21_20 (hp : 20 < (Q2.transData.getD 21 []).length)
    (j : Nat) (hj : j < (repChars.getD 21 []).length)
    (hq : (normIsRep.getD 21 []).getD j false = true) :
    species (Q2.reps (⟨21, by decide⟩ : Fin 148)) (colE2 ⟨21, by decide⟩ 20 hp)
        (rowE2 (⟨21, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨21, by decide⟩ : Fin 148))
        (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp))
        (rowE1 (⟨21, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨21, by decide⟩ : Fin 148) ⟨21, by decide⟩ _
      (validAt ⟨21, by decide⟩ (listedAt ⟨21, by decide⟩ hj))
      (colE1 ⟨21, by decide⟩ 20 (transLenTr ⟨21, by decide⟩ 20 hp)) T21_21
      hfix21_21 hinj21_21 hcardT21_21
      (fun i => conj_mem_of_fixedPoints _ _ (T21_21 i) (hfix21_21 i) _)
      ⟨21, by decide⟩ ⟨21, by decide⟩ _
      (Q2.validAt ⟨21, by decide⟩ (Q2.listedAt ⟨21, by decide⟩
        (alnCheck_rep ⟨21, by decide⟩ hj hq).1))
      (colE2 ⟨21, by decide⟩ 20 hp) Q2.T21_21_2 Q2.hfix21_21_2 Q2.hinj21_21_2
      Q2.hcardT21_21_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T21_21_2 i) (Q2.hfix21_21_2 i) _)
      colCert_21_21_20.hD ?_).symm
  rw [alnId_21 j hj]


theorem leaf_22_4_0 (hp : 0 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 0 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 0 (transLenTr ⟨4, by decide⟩ 0 hp)) T22_4
      hfix22_4 hinj22_4 hcardT22_4
      (fun i => conj_mem_of_fixedPoints _ _ (T22_4 i) (hfix22_4 i) _)
      ⟨22, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 0 hp) Q2.T22_4_2 Q2.hfix22_4_2 Q2.hinj22_4_2
      Q2.hcardT22_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_4_2 i) (Q2.hfix22_4_2 i) _)
      colCert_22_4_0.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_4_1 (hp : 1 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 1 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 1 (transLenTr ⟨4, by decide⟩ 1 hp)) T22_4
      hfix22_4 hinj22_4 hcardT22_4
      (fun i => conj_mem_of_fixedPoints _ _ (T22_4 i) (hfix22_4 i) _)
      ⟨22, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 1 hp) Q2.T22_4_2 Q2.hfix22_4_2 Q2.hinj22_4_2
      Q2.hcardT22_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_4_2 i) (Q2.hfix22_4_2 i) _)
      colCert_22_4_1.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_4_2 (hp : 2 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 2 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 2 (transLenTr ⟨4, by decide⟩ 2 hp)) T22_4
      hfix22_4 hinj22_4 hcardT22_4
      (fun i => conj_mem_of_fixedPoints _ _ (T22_4 i) (hfix22_4 i) _)
      ⟨22, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 2 hp) Q2.T22_4_2 Q2.hfix22_4_2 Q2.hinj22_4_2
      Q2.hcardT22_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_4_2 i) (Q2.hfix22_4_2 i) _)
      colCert_22_4_2.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_4_3 (hp : 3 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 3 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 3 (transLenTr ⟨4, by decide⟩ 3 hp)) T22_4
      hfix22_4 hinj22_4 hcardT22_4
      (fun i => conj_mem_of_fixedPoints _ _ (T22_4 i) (hfix22_4 i) _)
      ⟨22, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 3 hp) Q2.T22_4_2 Q2.hfix22_4_2 Q2.hinj22_4_2
      Q2.hcardT22_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_4_2 i) (Q2.hfix22_4_2 i) _)
      colCert_22_4_3.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_4_4 (hp : 4 < (Q2.transData.getD 4 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨4, by decide⟩ : Fin 148)) (colE2 ⟨4, by decide⟩ 4 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨4, by decide⟩ : Fin 148))
        (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨4, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨4, by decide⟩ 4 (transLenTr ⟨4, by decide⟩ 4 hp)) T22_4
      hfix22_4 hinj22_4 hcardT22_4
      (fun i => conj_mem_of_fixedPoints _ _ (T22_4 i) (hfix22_4 i) _)
      ⟨22, by decide⟩ ⟨4, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨4, by decide⟩ 4 hp) Q2.T22_4_2 Q2.hfix22_4_2 Q2.hinj22_4_2
      Q2.hcardT22_4_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_4_2 i) (Q2.hfix22_4_2 i) _)
      colCert_22_4_4.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T22_12
      hfix22_12 hinj22_12 hcardT22_12
      (fun i => conj_mem_of_fixedPoints _ _ (T22_12 i) (hfix22_12 i) _)
      ⟨22, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T22_12_2 Q2.hfix22_12_2 Q2.hinj22_12_2
      Q2.hcardT22_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_12_2 i) (Q2.hfix22_12_2 i) _)
      colCert_22_12_0.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T22_12
      hfix22_12 hinj22_12 hcardT22_12
      (fun i => conj_mem_of_fixedPoints _ _ (T22_12 i) (hfix22_12 i) _)
      ⟨22, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T22_12_2 Q2.hfix22_12_2 Q2.hinj22_12_2
      Q2.hcardT22_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_12_2 i) (Q2.hfix22_12_2 i) _)
      colCert_22_12_1.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T22_12
      hfix22_12 hinj22_12 hcardT22_12
      (fun i => conj_mem_of_fixedPoints _ _ (T22_12 i) (hfix22_12 i) _)
      ⟨22, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T22_12_2 Q2.hfix22_12_2 Q2.hinj22_12_2
      Q2.hcardT22_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_12_2 i) (Q2.hfix22_12_2 i) _)
      colCert_22_12_2.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T22_12
      hfix22_12 hinj22_12 hcardT22_12
      (fun i => conj_mem_of_fixedPoints _ _ (T22_12 i) (hfix22_12 i) _)
      ⟨22, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T22_12_2 Q2.hfix22_12_2 Q2.hinj22_12_2
      Q2.hcardT22_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_12_2 i) (Q2.hfix22_12_2 i) _)
      colCert_22_12_3.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T22_12
      hfix22_12 hinj22_12 hcardT22_12
      (fun i => conj_mem_of_fixedPoints _ _ (T22_12 i) (hfix22_12 i) _)
      ⟨22, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T22_12_2 Q2.hfix22_12_2 Q2.hinj22_12_2
      Q2.hcardT22_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_12_2 i) (Q2.hfix22_12_2 i) _)
      colCert_22_12_4.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_22_0 (hp : 0 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 0 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 0 (transLenTr ⟨22, by decide⟩ 0 hp)) T22_22
      hfix22_22 hinj22_22 hcardT22_22
      (fun i => conj_mem_of_fixedPoints _ _ (T22_22 i) (hfix22_22 i) _)
      ⟨22, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 0 hp) Q2.T22_22_2 Q2.hfix22_22_2 Q2.hinj22_22_2
      Q2.hcardT22_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_22_2 i) (Q2.hfix22_22_2 i) _)
      colCert_22_22_0.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_22_1 (hp : 1 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 1 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 1 (transLenTr ⟨22, by decide⟩ 1 hp)) T22_22
      hfix22_22 hinj22_22 hcardT22_22
      (fun i => conj_mem_of_fixedPoints _ _ (T22_22 i) (hfix22_22 i) _)
      ⟨22, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 1 hp) Q2.T22_22_2 Q2.hfix22_22_2 Q2.hinj22_22_2
      Q2.hcardT22_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_22_2 i) (Q2.hfix22_22_2 i) _)
      colCert_22_22_1.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_22_2 (hp : 2 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 2 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 2 (transLenTr ⟨22, by decide⟩ 2 hp)) T22_22
      hfix22_22 hinj22_22 hcardT22_22
      (fun i => conj_mem_of_fixedPoints _ _ (T22_22 i) (hfix22_22 i) _)
      ⟨22, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 2 hp) Q2.T22_22_2 Q2.hfix22_22_2 Q2.hinj22_22_2
      Q2.hcardT22_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_22_2 i) (Q2.hfix22_22_2 i) _)
      colCert_22_22_2.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_22_3 (hp : 3 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 3 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 3 (transLenTr ⟨22, by decide⟩ 3 hp)) T22_22
      hfix22_22 hinj22_22 hcardT22_22
      (fun i => conj_mem_of_fixedPoints _ _ (T22_22 i) (hfix22_22 i) _)
      ⟨22, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 3 hp) Q2.T22_22_2 Q2.hfix22_22_2 Q2.hinj22_22_2
      Q2.hcardT22_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_22_2 i) (Q2.hfix22_22_2 i) _)
      colCert_22_22_3.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_22_4 (hp : 4 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 4 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 4 (transLenTr ⟨22, by decide⟩ 4 hp)) T22_22
      hfix22_22 hinj22_22 hcardT22_22
      (fun i => conj_mem_of_fixedPoints _ _ (T22_22 i) (hfix22_22 i) _)
      ⟨22, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 4 hp) Q2.T22_22_2 Q2.hfix22_22_2 Q2.hinj22_22_2
      Q2.hcardT22_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_22_2 i) (Q2.hfix22_22_2 i) _)
      colCert_22_22_4.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_22_5 (hp : 5 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 5 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 5 (transLenTr ⟨22, by decide⟩ 5 hp)) T22_22
      hfix22_22 hinj22_22 hcardT22_22
      (fun i => conj_mem_of_fixedPoints _ _ (T22_22 i) (hfix22_22 i) _)
      ⟨22, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 5 hp) Q2.T22_22_2 Q2.hfix22_22_2 Q2.hinj22_22_2
      Q2.hcardT22_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_22_2 i) (Q2.hfix22_22_2 i) _)
      colCert_22_22_5.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_22_10 (hp : 10 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 10 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 10 (transLenTr ⟨22, by decide⟩ 10 hp)) T22_22
      hfix22_22 hinj22_22 hcardT22_22
      (fun i => conj_mem_of_fixedPoints _ _ (T22_22 i) (hfix22_22 i) _)
      ⟨22, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 10 hp) Q2.T22_22_2 Q2.hfix22_22_2 Q2.hinj22_22_2
      Q2.hcardT22_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_22_2 i) (Q2.hfix22_22_2 i) _)
      colCert_22_22_10.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_22_15 (hp : 15 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 15 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 15 (transLenTr ⟨22, by decide⟩ 15 hp)) T22_22
      hfix22_22 hinj22_22 hcardT22_22
      (fun i => conj_mem_of_fixedPoints _ _ (T22_22 i) (hfix22_22 i) _)
      ⟨22, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 15 hp) Q2.T22_22_2 Q2.hfix22_22_2 Q2.hinj22_22_2
      Q2.hcardT22_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_22_2 i) (Q2.hfix22_22_2 i) _)
      colCert_22_22_15.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_22_22_20 (hp : 20 < (Q2.transData.getD 22 []).length)
    (j : Nat) (hj : j < (repChars.getD 22 []).length)
    (hq : (normIsRep.getD 22 []).getD j false = true) :
    species (Q2.reps (⟨22, by decide⟩ : Fin 148)) (colE2 ⟨22, by decide⟩ 20 hp)
        (rowE2 (⟨22, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨22, by decide⟩ : Fin 148))
        (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp))
        (rowE1 (⟨22, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨22, by decide⟩ : Fin 148) ⟨22, by decide⟩ _
      (validAt ⟨22, by decide⟩ (listedAt ⟨22, by decide⟩ hj))
      (colE1 ⟨22, by decide⟩ 20 (transLenTr ⟨22, by decide⟩ 20 hp)) T22_22
      hfix22_22 hinj22_22 hcardT22_22
      (fun i => conj_mem_of_fixedPoints _ _ (T22_22 i) (hfix22_22 i) _)
      ⟨22, by decide⟩ ⟨22, by decide⟩ _
      (Q2.validAt ⟨22, by decide⟩ (Q2.listedAt ⟨22, by decide⟩
        (alnCheck_rep ⟨22, by decide⟩ hj hq).1))
      (colE2 ⟨22, by decide⟩ 20 hp) Q2.T22_22_2 Q2.hfix22_22_2 Q2.hinj22_22_2
      Q2.hcardT22_22_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T22_22_2 i) (Q2.hfix22_22_2 i) _)
      colCert_22_22_20.hD ?_).symm
  rw [alnId_22 j hj]


theorem leaf_23_5_0 (hp : 0 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 0 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 0 (transLenTr ⟨5, by decide⟩ 0 hp)) T23_5
      hfix23_5 hinj23_5 hcardT23_5
      (fun i => conj_mem_of_fixedPoints _ _ (T23_5 i) (hfix23_5 i) _)
      ⟨23, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 0 hp) Q2.T23_5_2 Q2.hfix23_5_2 Q2.hinj23_5_2
      Q2.hcardT23_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_5_2 i) (Q2.hfix23_5_2 i) _)
      colCert_23_5_0.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_5_1 (hp : 1 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 1 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 1 (transLenTr ⟨5, by decide⟩ 1 hp)) T23_5
      hfix23_5 hinj23_5 hcardT23_5
      (fun i => conj_mem_of_fixedPoints _ _ (T23_5 i) (hfix23_5 i) _)
      ⟨23, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 1 hp) Q2.T23_5_2 Q2.hfix23_5_2 Q2.hinj23_5_2
      Q2.hcardT23_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_5_2 i) (Q2.hfix23_5_2 i) _)
      colCert_23_5_1.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_5_2 (hp : 2 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 2 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 2 (transLenTr ⟨5, by decide⟩ 2 hp)) T23_5
      hfix23_5 hinj23_5 hcardT23_5
      (fun i => conj_mem_of_fixedPoints _ _ (T23_5 i) (hfix23_5 i) _)
      ⟨23, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 2 hp) Q2.T23_5_2 Q2.hfix23_5_2 Q2.hinj23_5_2
      Q2.hcardT23_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_5_2 i) (Q2.hfix23_5_2 i) _)
      colCert_23_5_2.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_5_3 (hp : 3 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 3 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 3 (transLenTr ⟨5, by decide⟩ 3 hp)) T23_5
      hfix23_5 hinj23_5 hcardT23_5
      (fun i => conj_mem_of_fixedPoints _ _ (T23_5 i) (hfix23_5 i) _)
      ⟨23, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 3 hp) Q2.T23_5_2 Q2.hfix23_5_2 Q2.hinj23_5_2
      Q2.hcardT23_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_5_2 i) (Q2.hfix23_5_2 i) _)
      colCert_23_5_3.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_5_4 (hp : 4 < (Q2.transData.getD 5 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨5, by decide⟩ : Fin 148)) (colE2 ⟨5, by decide⟩ 4 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨5, by decide⟩ : Fin 148))
        (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨5, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨5, by decide⟩ 4 (transLenTr ⟨5, by decide⟩ 4 hp)) T23_5
      hfix23_5 hinj23_5 hcardT23_5
      (fun i => conj_mem_of_fixedPoints _ _ (T23_5 i) (hfix23_5 i) _)
      ⟨23, by decide⟩ ⟨5, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨5, by decide⟩ 4 hp) Q2.T23_5_2 Q2.hfix23_5_2 Q2.hinj23_5_2
      Q2.hcardT23_5_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_5_2 i) (Q2.hfix23_5_2 i) _)
      colCert_23_5_4.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T23_12
      hfix23_12 hinj23_12 hcardT23_12
      (fun i => conj_mem_of_fixedPoints _ _ (T23_12 i) (hfix23_12 i) _)
      ⟨23, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T23_12_2 Q2.hfix23_12_2 Q2.hinj23_12_2
      Q2.hcardT23_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_12_2 i) (Q2.hfix23_12_2 i) _)
      colCert_23_12_0.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T23_12
      hfix23_12 hinj23_12 hcardT23_12
      (fun i => conj_mem_of_fixedPoints _ _ (T23_12 i) (hfix23_12 i) _)
      ⟨23, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T23_12_2 Q2.hfix23_12_2 Q2.hinj23_12_2
      Q2.hcardT23_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_12_2 i) (Q2.hfix23_12_2 i) _)
      colCert_23_12_1.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T23_12
      hfix23_12 hinj23_12 hcardT23_12
      (fun i => conj_mem_of_fixedPoints _ _ (T23_12 i) (hfix23_12 i) _)
      ⟨23, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T23_12_2 Q2.hfix23_12_2 Q2.hinj23_12_2
      Q2.hcardT23_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_12_2 i) (Q2.hfix23_12_2 i) _)
      colCert_23_12_2.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T23_12
      hfix23_12 hinj23_12 hcardT23_12
      (fun i => conj_mem_of_fixedPoints _ _ (T23_12 i) (hfix23_12 i) _)
      ⟨23, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T23_12_2 Q2.hfix23_12_2 Q2.hinj23_12_2
      Q2.hcardT23_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_12_2 i) (Q2.hfix23_12_2 i) _)
      colCert_23_12_3.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T23_12
      hfix23_12 hinj23_12 hcardT23_12
      (fun i => conj_mem_of_fixedPoints _ _ (T23_12 i) (hfix23_12 i) _)
      ⟨23, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T23_12_2 Q2.hfix23_12_2 Q2.hinj23_12_2
      Q2.hcardT23_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_12_2 i) (Q2.hfix23_12_2 i) _)
      colCert_23_12_4.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_23_0 (hp : 0 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 0 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 0 (transLenTr ⟨23, by decide⟩ 0 hp)) T23_23
      hfix23_23 hinj23_23 hcardT23_23
      (fun i => conj_mem_of_fixedPoints _ _ (T23_23 i) (hfix23_23 i) _)
      ⟨23, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 0 hp) Q2.T23_23_2 Q2.hfix23_23_2 Q2.hinj23_23_2
      Q2.hcardT23_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_23_2 i) (Q2.hfix23_23_2 i) _)
      colCert_23_23_0.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_23_1 (hp : 1 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 1 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 1 (transLenTr ⟨23, by decide⟩ 1 hp)) T23_23
      hfix23_23 hinj23_23 hcardT23_23
      (fun i => conj_mem_of_fixedPoints _ _ (T23_23 i) (hfix23_23 i) _)
      ⟨23, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 1 hp) Q2.T23_23_2 Q2.hfix23_23_2 Q2.hinj23_23_2
      Q2.hcardT23_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_23_2 i) (Q2.hfix23_23_2 i) _)
      colCert_23_23_1.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_23_2 (hp : 2 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 2 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 2 (transLenTr ⟨23, by decide⟩ 2 hp)) T23_23
      hfix23_23 hinj23_23 hcardT23_23
      (fun i => conj_mem_of_fixedPoints _ _ (T23_23 i) (hfix23_23 i) _)
      ⟨23, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 2 hp) Q2.T23_23_2 Q2.hfix23_23_2 Q2.hinj23_23_2
      Q2.hcardT23_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_23_2 i) (Q2.hfix23_23_2 i) _)
      colCert_23_23_2.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_23_3 (hp : 3 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 3 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 3 (transLenTr ⟨23, by decide⟩ 3 hp)) T23_23
      hfix23_23 hinj23_23 hcardT23_23
      (fun i => conj_mem_of_fixedPoints _ _ (T23_23 i) (hfix23_23 i) _)
      ⟨23, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 3 hp) Q2.T23_23_2 Q2.hfix23_23_2 Q2.hinj23_23_2
      Q2.hcardT23_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_23_2 i) (Q2.hfix23_23_2 i) _)
      colCert_23_23_3.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_23_4 (hp : 4 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 4 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 4 (transLenTr ⟨23, by decide⟩ 4 hp)) T23_23
      hfix23_23 hinj23_23 hcardT23_23
      (fun i => conj_mem_of_fixedPoints _ _ (T23_23 i) (hfix23_23 i) _)
      ⟨23, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 4 hp) Q2.T23_23_2 Q2.hfix23_23_2 Q2.hinj23_23_2
      Q2.hcardT23_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_23_2 i) (Q2.hfix23_23_2 i) _)
      colCert_23_23_4.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_23_5 (hp : 5 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 5 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 5 (transLenTr ⟨23, by decide⟩ 5 hp)) T23_23
      hfix23_23 hinj23_23 hcardT23_23
      (fun i => conj_mem_of_fixedPoints _ _ (T23_23 i) (hfix23_23 i) _)
      ⟨23, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 5 hp) Q2.T23_23_2 Q2.hfix23_23_2 Q2.hinj23_23_2
      Q2.hcardT23_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_23_2 i) (Q2.hfix23_23_2 i) _)
      colCert_23_23_5.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_23_10 (hp : 10 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 10 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 10 (transLenTr ⟨23, by decide⟩ 10 hp)) T23_23
      hfix23_23 hinj23_23 hcardT23_23
      (fun i => conj_mem_of_fixedPoints _ _ (T23_23 i) (hfix23_23 i) _)
      ⟨23, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 10 hp) Q2.T23_23_2 Q2.hfix23_23_2 Q2.hinj23_23_2
      Q2.hcardT23_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_23_2 i) (Q2.hfix23_23_2 i) _)
      colCert_23_23_10.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_23_15 (hp : 15 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 15 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 15 (transLenTr ⟨23, by decide⟩ 15 hp)) T23_23
      hfix23_23 hinj23_23 hcardT23_23
      (fun i => conj_mem_of_fixedPoints _ _ (T23_23 i) (hfix23_23 i) _)
      ⟨23, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 15 hp) Q2.T23_23_2 Q2.hfix23_23_2 Q2.hinj23_23_2
      Q2.hcardT23_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_23_2 i) (Q2.hfix23_23_2 i) _)
      colCert_23_23_15.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_23_23_20 (hp : 20 < (Q2.transData.getD 23 []).length)
    (j : Nat) (hj : j < (repChars.getD 23 []).length)
    (hq : (normIsRep.getD 23 []).getD j false = true) :
    species (Q2.reps (⟨23, by decide⟩ : Fin 148)) (colE2 ⟨23, by decide⟩ 20 hp)
        (rowE2 (⟨23, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨23, by decide⟩ : Fin 148))
        (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp))
        (rowE1 (⟨23, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨23, by decide⟩ : Fin 148) ⟨23, by decide⟩ _
      (validAt ⟨23, by decide⟩ (listedAt ⟨23, by decide⟩ hj))
      (colE1 ⟨23, by decide⟩ 20 (transLenTr ⟨23, by decide⟩ 20 hp)) T23_23
      hfix23_23 hinj23_23 hcardT23_23
      (fun i => conj_mem_of_fixedPoints _ _ (T23_23 i) (hfix23_23 i) _)
      ⟨23, by decide⟩ ⟨23, by decide⟩ _
      (Q2.validAt ⟨23, by decide⟩ (Q2.listedAt ⟨23, by decide⟩
        (alnCheck_rep ⟨23, by decide⟩ hj hq).1))
      (colE2 ⟨23, by decide⟩ 20 hp) Q2.T23_23_2 Q2.hfix23_23_2 Q2.hinj23_23_2
      Q2.hcardT23_23_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T23_23_2 i) (Q2.hfix23_23_2 i) _)
      colCert_23_23_20.hD ?_).symm
  rw [alnId_23 j hj]


theorem leaf_24_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T24_6
      hfix24_6 hinj24_6 hcardT24_6
      (fun i => conj_mem_of_fixedPoints _ _ (T24_6 i) (hfix24_6 i) _)
      ⟨24, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T24_6_2 Q2.hfix24_6_2 Q2.hinj24_6_2
      Q2.hcardT24_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_6_2 i) (Q2.hfix24_6_2 i) _)
      colCert_24_6_0.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T24_6
      hfix24_6 hinj24_6 hcardT24_6
      (fun i => conj_mem_of_fixedPoints _ _ (T24_6 i) (hfix24_6 i) _)
      ⟨24, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T24_6_2 Q2.hfix24_6_2 Q2.hinj24_6_2
      Q2.hcardT24_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_6_2 i) (Q2.hfix24_6_2 i) _)
      colCert_24_6_1.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T24_6
      hfix24_6 hinj24_6 hcardT24_6
      (fun i => conj_mem_of_fixedPoints _ _ (T24_6 i) (hfix24_6 i) _)
      ⟨24, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T24_6_2 Q2.hfix24_6_2 Q2.hinj24_6_2
      Q2.hcardT24_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_6_2 i) (Q2.hfix24_6_2 i) _)
      colCert_24_6_2.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T24_6
      hfix24_6 hinj24_6 hcardT24_6
      (fun i => conj_mem_of_fixedPoints _ _ (T24_6 i) (hfix24_6 i) _)
      ⟨24, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T24_6_2 Q2.hfix24_6_2 Q2.hinj24_6_2
      Q2.hcardT24_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_6_2 i) (Q2.hfix24_6_2 i) _)
      colCert_24_6_3.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T24_6
      hfix24_6 hinj24_6 hcardT24_6
      (fun i => conj_mem_of_fixedPoints _ _ (T24_6 i) (hfix24_6 i) _)
      ⟨24, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T24_6_2 Q2.hfix24_6_2 Q2.hinj24_6_2
      Q2.hcardT24_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_6_2 i) (Q2.hfix24_6_2 i) _)
      colCert_24_6_4.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T24_12
      hfix24_12 hinj24_12 hcardT24_12
      (fun i => conj_mem_of_fixedPoints _ _ (T24_12 i) (hfix24_12 i) _)
      ⟨24, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T24_12_2 Q2.hfix24_12_2 Q2.hinj24_12_2
      Q2.hcardT24_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_12_2 i) (Q2.hfix24_12_2 i) _)
      colCert_24_12_0.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T24_12
      hfix24_12 hinj24_12 hcardT24_12
      (fun i => conj_mem_of_fixedPoints _ _ (T24_12 i) (hfix24_12 i) _)
      ⟨24, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T24_12_2 Q2.hfix24_12_2 Q2.hinj24_12_2
      Q2.hcardT24_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_12_2 i) (Q2.hfix24_12_2 i) _)
      colCert_24_12_1.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T24_12
      hfix24_12 hinj24_12 hcardT24_12
      (fun i => conj_mem_of_fixedPoints _ _ (T24_12 i) (hfix24_12 i) _)
      ⟨24, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T24_12_2 Q2.hfix24_12_2 Q2.hinj24_12_2
      Q2.hcardT24_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_12_2 i) (Q2.hfix24_12_2 i) _)
      colCert_24_12_2.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T24_12
      hfix24_12 hinj24_12 hcardT24_12
      (fun i => conj_mem_of_fixedPoints _ _ (T24_12 i) (hfix24_12 i) _)
      ⟨24, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T24_12_2 Q2.hfix24_12_2 Q2.hinj24_12_2
      Q2.hcardT24_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_12_2 i) (Q2.hfix24_12_2 i) _)
      colCert_24_12_3.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T24_12
      hfix24_12 hinj24_12 hcardT24_12
      (fun i => conj_mem_of_fixedPoints _ _ (T24_12 i) (hfix24_12 i) _)
      ⟨24, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T24_12_2 Q2.hfix24_12_2 Q2.hinj24_12_2
      Q2.hcardT24_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_12_2 i) (Q2.hfix24_12_2 i) _)
      colCert_24_12_4.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T24_24
      hfix24_24 hinj24_24 hcardT24_24
      (fun i => conj_mem_of_fixedPoints _ _ (T24_24 i) (hfix24_24 i) _)
      ⟨24, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T24_24_2 Q2.hfix24_24_2 Q2.hinj24_24_2
      Q2.hcardT24_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_24_2 i) (Q2.hfix24_24_2 i) _)
      colCert_24_24_0.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T24_24
      hfix24_24 hinj24_24 hcardT24_24
      (fun i => conj_mem_of_fixedPoints _ _ (T24_24 i) (hfix24_24 i) _)
      ⟨24, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T24_24_2 Q2.hfix24_24_2 Q2.hinj24_24_2
      Q2.hcardT24_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_24_2 i) (Q2.hfix24_24_2 i) _)
      colCert_24_24_1.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T24_24
      hfix24_24 hinj24_24 hcardT24_24
      (fun i => conj_mem_of_fixedPoints _ _ (T24_24 i) (hfix24_24 i) _)
      ⟨24, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T24_24_2 Q2.hfix24_24_2 Q2.hinj24_24_2
      Q2.hcardT24_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_24_2 i) (Q2.hfix24_24_2 i) _)
      colCert_24_24_2.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T24_24
      hfix24_24 hinj24_24 hcardT24_24
      (fun i => conj_mem_of_fixedPoints _ _ (T24_24 i) (hfix24_24 i) _)
      ⟨24, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T24_24_2 Q2.hfix24_24_2 Q2.hinj24_24_2
      Q2.hcardT24_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_24_2 i) (Q2.hfix24_24_2 i) _)
      colCert_24_24_3.hD ?_).symm
  rw [alnId_24 j hj]


theorem leaf_24_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 24 []).length)
    (hq : (normIsRep.getD 24 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨24, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨24, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨24, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨24, by decide⟩ (listedAt ⟨24, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T24_24
      hfix24_24 hinj24_24 hcardT24_24
      (fun i => conj_mem_of_fixedPoints _ _ (T24_24 i) (hfix24_24 i) _)
      ⟨24, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨24, by decide⟩ (Q2.listedAt ⟨24, by decide⟩
        (alnCheck_rep ⟨24, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T24_24_2 Q2.hfix24_24_2 Q2.hinj24_24_2
      Q2.hcardT24_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T24_24_2 i) (Q2.hfix24_24_2 i) _)
      colCert_24_24_4.hD ?_).symm
  rw [alnId_24 j hj]


end LeanDring.P5Presentation
