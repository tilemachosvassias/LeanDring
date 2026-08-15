/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C039
import LeanDring.P5.Data.ColCdd.C040
import LeanDring.P5.Data.ColRestCheap.C163
import LeanDring.P5.Data.ColRestCheap.C164
import LeanDring.P5.Data.ColRestCheap.C165
import LeanDring.P5.Data.ColRestCheap.C166
import LeanDring.P5.Data.EntryK.C017
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesAlign.C017
import LeanDring.P5.Data.SpeciesAlign.C018
import LeanDring.P5.Data.SpeciesAlign.C019
import LeanDring.P5.Data.SpeciesDiv.C048

/-! # Stage-5 leaves, chunk 10 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_71_71_23 (hp : 23 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 23 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 23 (transLenTr ⟨71, by decide⟩ 23 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 23 (transLenTr ⟨71, by decide⟩ 23 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 23 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_23.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_71_71_24 (hp : 24 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 71 []).length)
    (hq : (normIsRep.getD 71 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 24 hp)
        (rowE2 (⟨71, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 24 (transLenTr ⟨71, by decide⟩ 24 hp))
        (rowE1 (⟨71, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨71, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨71, by decide⟩ (listedAt ⟨71, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 24 (transLenTr ⟨71, by decide⟩ 24 hp)) T71_71
      hfix71_71 hinj71_71 hcardT71_71
      (fun i => conj_mem_of_fixedPoints _ _ (T71_71 i) (hfix71_71 i) _)
      ⟨71, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨71, by decide⟩ (Q2.listedAt ⟨71, by decide⟩
        (alnCheck_rep ⟨71, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 24 hp) Q2.T71_71_2 Q2.hfix71_71_2 Q2.hinj71_71_2
      Q2.hcardT71_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T71_71_2 i) (Q2.hfix71_71_2 i) _)
      colCert_71_71_24.hD ?_).symm
  rw [alnId_71 j hj]


theorem leaf_72_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T72_7
      hfix72_7 hinj72_7 hcardT72_7
      (fun i => conj_mem_of_fixedPoints _ _ (T72_7 i) (hfix72_7 i) _)
      ⟨72, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T72_7_2 Q2.hfix72_7_2 Q2.hinj72_7_2
      Q2.hcardT72_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_7_2 i) (Q2.hfix72_7_2 i) _)
      colCert_72_7_0.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T72_7
      hfix72_7 hinj72_7 hcardT72_7
      (fun i => conj_mem_of_fixedPoints _ _ (T72_7 i) (hfix72_7 i) _)
      ⟨72, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T72_7_2 Q2.hfix72_7_2 Q2.hinj72_7_2
      Q2.hcardT72_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_7_2 i) (Q2.hfix72_7_2 i) _)
      colCert_72_7_1.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T72_7
      hfix72_7 hinj72_7 hcardT72_7
      (fun i => conj_mem_of_fixedPoints _ _ (T72_7 i) (hfix72_7 i) _)
      ⟨72, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T72_7_2 Q2.hfix72_7_2 Q2.hinj72_7_2
      Q2.hcardT72_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_7_2 i) (Q2.hfix72_7_2 i) _)
      colCert_72_7_2.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T72_7
      hfix72_7 hinj72_7 hcardT72_7
      (fun i => conj_mem_of_fixedPoints _ _ (T72_7 i) (hfix72_7 i) _)
      ⟨72, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T72_7_2 Q2.hfix72_7_2 Q2.hinj72_7_2
      Q2.hcardT72_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_7_2 i) (Q2.hfix72_7_2 i) _)
      colCert_72_7_3.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T72_7
      hfix72_7 hinj72_7 hcardT72_7
      (fun i => conj_mem_of_fixedPoints _ _ (T72_7 i) (hfix72_7 i) _)
      ⟨72, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T72_7_2 Q2.hfix72_7_2 Q2.hinj72_7_2
      Q2.hcardT72_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_7_2 i) (Q2.hfix72_7_2 i) _)
      colCert_72_7_4.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T72_12
      hfix72_12 hinj72_12 hcardT72_12
      (fun i => conj_mem_of_fixedPoints _ _ (T72_12 i) (hfix72_12 i) _)
      ⟨72, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T72_12_2 Q2.hfix72_12_2 Q2.hinj72_12_2
      Q2.hcardT72_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_12_2 i) (Q2.hfix72_12_2 i) _)
      colCert_72_12_0.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T72_12
      hfix72_12 hinj72_12 hcardT72_12
      (fun i => conj_mem_of_fixedPoints _ _ (T72_12 i) (hfix72_12 i) _)
      ⟨72, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T72_12_2 Q2.hfix72_12_2 Q2.hinj72_12_2
      Q2.hcardT72_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_12_2 i) (Q2.hfix72_12_2 i) _)
      colCert_72_12_1.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T72_12
      hfix72_12 hinj72_12 hcardT72_12
      (fun i => conj_mem_of_fixedPoints _ _ (T72_12 i) (hfix72_12 i) _)
      ⟨72, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T72_12_2 Q2.hfix72_12_2 Q2.hinj72_12_2
      Q2.hcardT72_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_12_2 i) (Q2.hfix72_12_2 i) _)
      colCert_72_12_2.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T72_12
      hfix72_12 hinj72_12 hcardT72_12
      (fun i => conj_mem_of_fixedPoints _ _ (T72_12 i) (hfix72_12 i) _)
      ⟨72, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T72_12_2 Q2.hfix72_12_2 Q2.hinj72_12_2
      Q2.hcardT72_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_12_2 i) (Q2.hfix72_12_2 i) _)
      colCert_72_12_3.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T72_12
      hfix72_12 hinj72_12 hcardT72_12
      (fun i => conj_mem_of_fixedPoints _ _ (T72_12 i) (hfix72_12 i) _)
      ⟨72, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T72_12_2 Q2.hfix72_12_2 Q2.hinj72_12_2
      Q2.hcardT72_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_12_2 i) (Q2.hfix72_12_2 i) _)
      colCert_72_12_4.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T72_25
      hfix72_25 hinj72_25 hcardT72_25
      (fun i => conj_mem_of_fixedPoints _ _ (T72_25 i) (hfix72_25 i) _)
      ⟨72, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T72_25_2 Q2.hfix72_25_2 Q2.hinj72_25_2
      Q2.hcardT72_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_25_2 i) (Q2.hfix72_25_2 i) _)
      colCert_72_25_0.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T72_25
      hfix72_25 hinj72_25 hcardT72_25
      (fun i => conj_mem_of_fixedPoints _ _ (T72_25 i) (hfix72_25 i) _)
      ⟨72, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T72_25_2 Q2.hfix72_25_2 Q2.hinj72_25_2
      Q2.hcardT72_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_25_2 i) (Q2.hfix72_25_2 i) _)
      colCert_72_25_1.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T72_25
      hfix72_25 hinj72_25 hcardT72_25
      (fun i => conj_mem_of_fixedPoints _ _ (T72_25 i) (hfix72_25 i) _)
      ⟨72, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T72_25_2 Q2.hfix72_25_2 Q2.hinj72_25_2
      Q2.hcardT72_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_25_2 i) (Q2.hfix72_25_2 i) _)
      colCert_72_25_2.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T72_25
      hfix72_25 hinj72_25 hcardT72_25
      (fun i => conj_mem_of_fixedPoints _ _ (T72_25 i) (hfix72_25 i) _)
      ⟨72, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T72_25_2 Q2.hfix72_25_2 Q2.hinj72_25_2
      Q2.hcardT72_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_25_2 i) (Q2.hfix72_25_2 i) _)
      colCert_72_25_3.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T72_25
      hfix72_25 hinj72_25 hcardT72_25
      (fun i => conj_mem_of_fixedPoints _ _ (T72_25 i) (hfix72_25 i) _)
      ⟨72, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T72_25_2 Q2.hfix72_25_2 Q2.hinj72_25_2
      Q2.hcardT72_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_25_2 i) (Q2.hfix72_25_2 i) _)
      colCert_72_25_4.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T72_25
      hfix72_25 hinj72_25 hcardT72_25
      (fun i => conj_mem_of_fixedPoints _ _ (T72_25 i) (hfix72_25 i) _)
      ⟨72, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T72_25_2 Q2.hfix72_25_2 Q2.hinj72_25_2
      Q2.hcardT72_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_25_2 i) (Q2.hfix72_25_2 i) _)
      colCert_72_25_5.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T72_25
      hfix72_25 hinj72_25 hcardT72_25
      (fun i => conj_mem_of_fixedPoints _ _ (T72_25 i) (hfix72_25 i) _)
      ⟨72, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T72_25_2 Q2.hfix72_25_2 Q2.hinj72_25_2
      Q2.hcardT72_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_25_2 i) (Q2.hfix72_25_2 i) _)
      colCert_72_25_10.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T72_25
      hfix72_25 hinj72_25 hcardT72_25
      (fun i => conj_mem_of_fixedPoints _ _ (T72_25 i) (hfix72_25 i) _)
      ⟨72, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T72_25_2 Q2.hfix72_25_2 Q2.hinj72_25_2
      Q2.hcardT72_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_25_2 i) (Q2.hfix72_25_2 i) _)
      colCert_72_25_15.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T72_25
      hfix72_25 hinj72_25 hcardT72_25
      (fun i => conj_mem_of_fixedPoints _ _ (T72_25 i) (hfix72_25 i) _)
      ⟨72, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T72_25_2 Q2.hfix72_25_2 Q2.hinj72_25_2
      Q2.hcardT72_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_25_2 i) (Q2.hfix72_25_2 i) _)
      colCert_72_25_20.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T72_31
      hfix72_31 hinj72_31 hcardT72_31
      (fun i => conj_mem_of_fixedPoints _ _ (T72_31 i) (hfix72_31 i) _)
      ⟨72, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T72_31_2 Q2.hfix72_31_2 Q2.hinj72_31_2
      Q2.hcardT72_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_31_2 i) (Q2.hfix72_31_2 i) _)
      colCert_72_31_0.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T72_31
      hfix72_31 hinj72_31 hcardT72_31
      (fun i => conj_mem_of_fixedPoints _ _ (T72_31 i) (hfix72_31 i) _)
      ⟨72, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T72_31_2 Q2.hfix72_31_2 Q2.hinj72_31_2
      Q2.hcardT72_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_31_2 i) (Q2.hfix72_31_2 i) _)
      colCert_72_31_1.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T72_31
      hfix72_31 hinj72_31 hcardT72_31
      (fun i => conj_mem_of_fixedPoints _ _ (T72_31 i) (hfix72_31 i) _)
      ⟨72, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T72_31_2 Q2.hfix72_31_2 Q2.hinj72_31_2
      Q2.hcardT72_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_31_2 i) (Q2.hfix72_31_2 i) _)
      colCert_72_31_2.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T72_31
      hfix72_31 hinj72_31 hcardT72_31
      (fun i => conj_mem_of_fixedPoints _ _ (T72_31 i) (hfix72_31 i) _)
      ⟨72, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T72_31_2 Q2.hfix72_31_2 Q2.hinj72_31_2
      Q2.hcardT72_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_31_2 i) (Q2.hfix72_31_2 i) _)
      colCert_72_31_3.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T72_31
      hfix72_31 hinj72_31 hcardT72_31
      (fun i => conj_mem_of_fixedPoints _ _ (T72_31 i) (hfix72_31 i) _)
      ⟨72, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T72_31_2 Q2.hfix72_31_2 Q2.hinj72_31_2
      Q2.hcardT72_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_31_2 i) (Q2.hfix72_31_2 i) _)
      colCert_72_31_4.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T72_31
      hfix72_31 hinj72_31 hcardT72_31
      (fun i => conj_mem_of_fixedPoints _ _ (T72_31 i) (hfix72_31 i) _)
      ⟨72, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T72_31_2 Q2.hfix72_31_2 Q2.hinj72_31_2
      Q2.hcardT72_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_31_2 i) (Q2.hfix72_31_2 i) _)
      colCert_72_31_5.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T72_31
      hfix72_31 hinj72_31 hcardT72_31
      (fun i => conj_mem_of_fixedPoints _ _ (T72_31 i) (hfix72_31 i) _)
      ⟨72, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T72_31_2 Q2.hfix72_31_2 Q2.hinj72_31_2
      Q2.hcardT72_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_31_2 i) (Q2.hfix72_31_2 i) _)
      colCert_72_31_10.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T72_31
      hfix72_31 hinj72_31 hcardT72_31
      (fun i => conj_mem_of_fixedPoints _ _ (T72_31 i) (hfix72_31 i) _)
      ⟨72, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T72_31_2 Q2.hfix72_31_2 Q2.hinj72_31_2
      Q2.hcardT72_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_31_2 i) (Q2.hfix72_31_2 i) _)
      colCert_72_31_15.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T72_31
      hfix72_31 hinj72_31 hcardT72_31
      (fun i => conj_mem_of_fixedPoints _ _ (T72_31 i) (hfix72_31 i) _)
      ⟨72, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T72_31_2 Q2.hfix72_31_2 Q2.hinj72_31_2
      Q2.hcardT72_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_31_2 i) (Q2.hfix72_31_2 i) _)
      colCert_72_31_20.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T72_36
      hfix72_36 hinj72_36 hcardT72_36
      (fun i => conj_mem_of_fixedPoints _ _ (T72_36 i) (hfix72_36 i) _)
      ⟨72, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T72_36_2 Q2.hfix72_36_2 Q2.hinj72_36_2
      Q2.hcardT72_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_36_2 i) (Q2.hfix72_36_2 i) _)
      colCert_72_36_0.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T72_36
      hfix72_36 hinj72_36 hcardT72_36
      (fun i => conj_mem_of_fixedPoints _ _ (T72_36 i) (hfix72_36 i) _)
      ⟨72, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T72_36_2 Q2.hfix72_36_2 Q2.hinj72_36_2
      Q2.hcardT72_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_36_2 i) (Q2.hfix72_36_2 i) _)
      colCert_72_36_1.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T72_36
      hfix72_36 hinj72_36 hcardT72_36
      (fun i => conj_mem_of_fixedPoints _ _ (T72_36 i) (hfix72_36 i) _)
      ⟨72, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T72_36_2 Q2.hfix72_36_2 Q2.hinj72_36_2
      Q2.hcardT72_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_36_2 i) (Q2.hfix72_36_2 i) _)
      colCert_72_36_2.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T72_36
      hfix72_36 hinj72_36 hcardT72_36
      (fun i => conj_mem_of_fixedPoints _ _ (T72_36 i) (hfix72_36 i) _)
      ⟨72, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T72_36_2 Q2.hfix72_36_2 Q2.hinj72_36_2
      Q2.hcardT72_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_36_2 i) (Q2.hfix72_36_2 i) _)
      colCert_72_36_3.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T72_36
      hfix72_36 hinj72_36 hcardT72_36
      (fun i => conj_mem_of_fixedPoints _ _ (T72_36 i) (hfix72_36 i) _)
      ⟨72, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T72_36_2 Q2.hfix72_36_2 Q2.hinj72_36_2
      Q2.hcardT72_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_36_2 i) (Q2.hfix72_36_2 i) _)
      colCert_72_36_4.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T72_36
      hfix72_36 hinj72_36 hcardT72_36
      (fun i => conj_mem_of_fixedPoints _ _ (T72_36 i) (hfix72_36 i) _)
      ⟨72, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T72_36_2 Q2.hfix72_36_2 Q2.hinj72_36_2
      Q2.hcardT72_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_36_2 i) (Q2.hfix72_36_2 i) _)
      colCert_72_36_5.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T72_36
      hfix72_36 hinj72_36 hcardT72_36
      (fun i => conj_mem_of_fixedPoints _ _ (T72_36 i) (hfix72_36 i) _)
      ⟨72, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T72_36_2 Q2.hfix72_36_2 Q2.hinj72_36_2
      Q2.hcardT72_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_36_2 i) (Q2.hfix72_36_2 i) _)
      colCert_72_36_10.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T72_36
      hfix72_36 hinj72_36 hcardT72_36
      (fun i => conj_mem_of_fixedPoints _ _ (T72_36 i) (hfix72_36 i) _)
      ⟨72, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T72_36_2 Q2.hfix72_36_2 Q2.hinj72_36_2
      Q2.hcardT72_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_36_2 i) (Q2.hfix72_36_2 i) _)
      colCert_72_36_15.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T72_36
      hfix72_36 hinj72_36 hcardT72_36
      (fun i => conj_mem_of_fixedPoints _ _ (T72_36 i) (hfix72_36 i) _)
      ⟨72, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T72_36_2 Q2.hfix72_36_2 Q2.hinj72_36_2
      Q2.hcardT72_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_36_2 i) (Q2.hfix72_36_2 i) _)
      colCert_72_36_20.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T72_41
      hfix72_41 hinj72_41 hcardT72_41
      (fun i => conj_mem_of_fixedPoints _ _ (T72_41 i) (hfix72_41 i) _)
      ⟨72, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T72_41_2 Q2.hfix72_41_2 Q2.hinj72_41_2
      Q2.hcardT72_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_41_2 i) (Q2.hfix72_41_2 i) _)
      colCert_72_41_0.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T72_41
      hfix72_41 hinj72_41 hcardT72_41
      (fun i => conj_mem_of_fixedPoints _ _ (T72_41 i) (hfix72_41 i) _)
      ⟨72, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T72_41_2 Q2.hfix72_41_2 Q2.hinj72_41_2
      Q2.hcardT72_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_41_2 i) (Q2.hfix72_41_2 i) _)
      colCert_72_41_1.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T72_41
      hfix72_41 hinj72_41 hcardT72_41
      (fun i => conj_mem_of_fixedPoints _ _ (T72_41 i) (hfix72_41 i) _)
      ⟨72, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T72_41_2 Q2.hfix72_41_2 Q2.hinj72_41_2
      Q2.hcardT72_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_41_2 i) (Q2.hfix72_41_2 i) _)
      colCert_72_41_2.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T72_41
      hfix72_41 hinj72_41 hcardT72_41
      (fun i => conj_mem_of_fixedPoints _ _ (T72_41 i) (hfix72_41 i) _)
      ⟨72, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T72_41_2 Q2.hfix72_41_2 Q2.hinj72_41_2
      Q2.hcardT72_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_41_2 i) (Q2.hfix72_41_2 i) _)
      colCert_72_41_3.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T72_41
      hfix72_41 hinj72_41 hcardT72_41
      (fun i => conj_mem_of_fixedPoints _ _ (T72_41 i) (hfix72_41 i) _)
      ⟨72, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T72_41_2 Q2.hfix72_41_2 Q2.hinj72_41_2
      Q2.hcardT72_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_41_2 i) (Q2.hfix72_41_2 i) _)
      colCert_72_41_4.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T72_41
      hfix72_41 hinj72_41 hcardT72_41
      (fun i => conj_mem_of_fixedPoints _ _ (T72_41 i) (hfix72_41 i) _)
      ⟨72, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T72_41_2 Q2.hfix72_41_2 Q2.hinj72_41_2
      Q2.hcardT72_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_41_2 i) (Q2.hfix72_41_2 i) _)
      colCert_72_41_5.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T72_41
      hfix72_41 hinj72_41 hcardT72_41
      (fun i => conj_mem_of_fixedPoints _ _ (T72_41 i) (hfix72_41 i) _)
      ⟨72, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T72_41_2 Q2.hfix72_41_2 Q2.hinj72_41_2
      Q2.hcardT72_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_41_2 i) (Q2.hfix72_41_2 i) _)
      colCert_72_41_10.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T72_41
      hfix72_41 hinj72_41 hcardT72_41
      (fun i => conj_mem_of_fixedPoints _ _ (T72_41 i) (hfix72_41 i) _)
      ⟨72, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T72_41_2 Q2.hfix72_41_2 Q2.hinj72_41_2
      Q2.hcardT72_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_41_2 i) (Q2.hfix72_41_2 i) _)
      colCert_72_41_15.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T72_41
      hfix72_41 hinj72_41 hcardT72_41
      (fun i => conj_mem_of_fixedPoints _ _ (T72_41 i) (hfix72_41 i) _)
      ⟨72, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T72_41_2 Q2.hfix72_41_2 Q2.hinj72_41_2
      Q2.hcardT72_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_41_2 i) (Q2.hfix72_41_2 i) _)
      colCert_72_41_20.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T72_46
      hfix72_46 hinj72_46 hcardT72_46
      (fun i => conj_mem_of_fixedPoints _ _ (T72_46 i) (hfix72_46 i) _)
      ⟨72, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T72_46_2 Q2.hfix72_46_2 Q2.hinj72_46_2
      Q2.hcardT72_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_46_2 i) (Q2.hfix72_46_2 i) _)
      colCert_72_46_0.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T72_46
      hfix72_46 hinj72_46 hcardT72_46
      (fun i => conj_mem_of_fixedPoints _ _ (T72_46 i) (hfix72_46 i) _)
      ⟨72, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T72_46_2 Q2.hfix72_46_2 Q2.hinj72_46_2
      Q2.hcardT72_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_46_2 i) (Q2.hfix72_46_2 i) _)
      colCert_72_46_1.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T72_46
      hfix72_46 hinj72_46 hcardT72_46
      (fun i => conj_mem_of_fixedPoints _ _ (T72_46 i) (hfix72_46 i) _)
      ⟨72, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T72_46_2 Q2.hfix72_46_2 Q2.hinj72_46_2
      Q2.hcardT72_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_46_2 i) (Q2.hfix72_46_2 i) _)
      colCert_72_46_2.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T72_46
      hfix72_46 hinj72_46 hcardT72_46
      (fun i => conj_mem_of_fixedPoints _ _ (T72_46 i) (hfix72_46 i) _)
      ⟨72, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T72_46_2 Q2.hfix72_46_2 Q2.hinj72_46_2
      Q2.hcardT72_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_46_2 i) (Q2.hfix72_46_2 i) _)
      colCert_72_46_3.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T72_46
      hfix72_46 hinj72_46 hcardT72_46
      (fun i => conj_mem_of_fixedPoints _ _ (T72_46 i) (hfix72_46 i) _)
      ⟨72, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T72_46_2 Q2.hfix72_46_2 Q2.hinj72_46_2
      Q2.hcardT72_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_46_2 i) (Q2.hfix72_46_2 i) _)
      colCert_72_46_4.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T72_46
      hfix72_46 hinj72_46 hcardT72_46
      (fun i => conj_mem_of_fixedPoints _ _ (T72_46 i) (hfix72_46 i) _)
      ⟨72, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T72_46_2 Q2.hfix72_46_2 Q2.hinj72_46_2
      Q2.hcardT72_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_46_2 i) (Q2.hfix72_46_2 i) _)
      colCert_72_46_5.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T72_46
      hfix72_46 hinj72_46 hcardT72_46
      (fun i => conj_mem_of_fixedPoints _ _ (T72_46 i) (hfix72_46 i) _)
      ⟨72, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T72_46_2 Q2.hfix72_46_2 Q2.hinj72_46_2
      Q2.hcardT72_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_46_2 i) (Q2.hfix72_46_2 i) _)
      colCert_72_46_10.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T72_46
      hfix72_46 hinj72_46 hcardT72_46
      (fun i => conj_mem_of_fixedPoints _ _ (T72_46 i) (hfix72_46 i) _)
      ⟨72, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T72_46_2 Q2.hfix72_46_2 Q2.hinj72_46_2
      Q2.hcardT72_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_46_2 i) (Q2.hfix72_46_2 i) _)
      colCert_72_46_15.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T72_46
      hfix72_46 hinj72_46 hcardT72_46
      (fun i => conj_mem_of_fixedPoints _ _ (T72_46 i) (hfix72_46 i) _)
      ⟨72, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T72_46_2 Q2.hfix72_46_2 Q2.hinj72_46_2
      Q2.hcardT72_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_46_2 i) (Q2.hfix72_46_2 i) _)
      colCert_72_46_20.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T72_51
      hfix72_51 hinj72_51 hcardT72_51
      (fun i => conj_mem_of_fixedPoints _ _ (T72_51 i) (hfix72_51 i) _)
      ⟨72, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T72_51_2 Q2.hfix72_51_2 Q2.hinj72_51_2
      Q2.hcardT72_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_51_2 i) (Q2.hfix72_51_2 i) _)
      colCert_72_51_0.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T72_51
      hfix72_51 hinj72_51 hcardT72_51
      (fun i => conj_mem_of_fixedPoints _ _ (T72_51 i) (hfix72_51 i) _)
      ⟨72, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T72_51_2 Q2.hfix72_51_2 Q2.hinj72_51_2
      Q2.hcardT72_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_51_2 i) (Q2.hfix72_51_2 i) _)
      colCert_72_51_1.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T72_51
      hfix72_51 hinj72_51 hcardT72_51
      (fun i => conj_mem_of_fixedPoints _ _ (T72_51 i) (hfix72_51 i) _)
      ⟨72, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T72_51_2 Q2.hfix72_51_2 Q2.hinj72_51_2
      Q2.hcardT72_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_51_2 i) (Q2.hfix72_51_2 i) _)
      colCert_72_51_2.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T72_51
      hfix72_51 hinj72_51 hcardT72_51
      (fun i => conj_mem_of_fixedPoints _ _ (T72_51 i) (hfix72_51 i) _)
      ⟨72, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T72_51_2 Q2.hfix72_51_2 Q2.hinj72_51_2
      Q2.hcardT72_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_51_2 i) (Q2.hfix72_51_2 i) _)
      colCert_72_51_3.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T72_51
      hfix72_51 hinj72_51 hcardT72_51
      (fun i => conj_mem_of_fixedPoints _ _ (T72_51 i) (hfix72_51 i) _)
      ⟨72, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T72_51_2 Q2.hfix72_51_2 Q2.hinj72_51_2
      Q2.hcardT72_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_51_2 i) (Q2.hfix72_51_2 i) _)
      colCert_72_51_4.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T72_51
      hfix72_51 hinj72_51 hcardT72_51
      (fun i => conj_mem_of_fixedPoints _ _ (T72_51 i) (hfix72_51 i) _)
      ⟨72, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T72_51_2 Q2.hfix72_51_2 Q2.hinj72_51_2
      Q2.hcardT72_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_51_2 i) (Q2.hfix72_51_2 i) _)
      colCert_72_51_5.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T72_51
      hfix72_51 hinj72_51 hcardT72_51
      (fun i => conj_mem_of_fixedPoints _ _ (T72_51 i) (hfix72_51 i) _)
      ⟨72, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T72_51_2 Q2.hfix72_51_2 Q2.hinj72_51_2
      Q2.hcardT72_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_51_2 i) (Q2.hfix72_51_2 i) _)
      colCert_72_51_10.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T72_51
      hfix72_51 hinj72_51 hcardT72_51
      (fun i => conj_mem_of_fixedPoints _ _ (T72_51 i) (hfix72_51 i) _)
      ⟨72, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T72_51_2 Q2.hfix72_51_2 Q2.hinj72_51_2
      Q2.hcardT72_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_51_2 i) (Q2.hfix72_51_2 i) _)
      colCert_72_51_15.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T72_51
      hfix72_51 hinj72_51 hcardT72_51
      (fun i => conj_mem_of_fixedPoints _ _ (T72_51 i) (hfix72_51 i) _)
      ⟨72, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T72_51_2 Q2.hfix72_51_2 Q2.hinj72_51_2
      Q2.hcardT72_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_51_2 i) (Q2.hfix72_51_2 i) _)
      colCert_72_51_20.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_0 (hp : 0 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 0 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 0 (transLenTr ⟨72, by decide⟩ 0 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 0 (transLenTr ⟨72, by decide⟩ 0 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 0 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_0.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_1 (hp : 1 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 1 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 1 (transLenTr ⟨72, by decide⟩ 1 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 1 (transLenTr ⟨72, by decide⟩ 1 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 1 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_1.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_2 (hp : 2 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 2 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 2 (transLenTr ⟨72, by decide⟩ 2 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 2 (transLenTr ⟨72, by decide⟩ 2 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 2 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_2.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_3 (hp : 3 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 3 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 3 (transLenTr ⟨72, by decide⟩ 3 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 3 (transLenTr ⟨72, by decide⟩ 3 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 3 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_3.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_4 (hp : 4 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 4 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 4 (transLenTr ⟨72, by decide⟩ 4 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 4 (transLenTr ⟨72, by decide⟩ 4 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 4 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_4.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_5 (hp : 5 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 5 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 5 (transLenTr ⟨72, by decide⟩ 5 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 5 (transLenTr ⟨72, by decide⟩ 5 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 5 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_5.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_6 (hp : 6 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 6 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 6 (transLenTr ⟨72, by decide⟩ 6 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 6 (transLenTr ⟨72, by decide⟩ 6 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 6 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_6.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_7 (hp : 7 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 7 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 7 (transLenTr ⟨72, by decide⟩ 7 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 7 (transLenTr ⟨72, by decide⟩ 7 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 7 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_7.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_8 (hp : 8 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 8 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 8 (transLenTr ⟨72, by decide⟩ 8 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 8 (transLenTr ⟨72, by decide⟩ 8 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 8 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_8.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_9 (hp : 9 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 9 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 9 (transLenTr ⟨72, by decide⟩ 9 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 9 (transLenTr ⟨72, by decide⟩ 9 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 9 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_9.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_10 (hp : 10 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 10 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 10 (transLenTr ⟨72, by decide⟩ 10 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 10 (transLenTr ⟨72, by decide⟩ 10 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 10 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_10.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_11 (hp : 11 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 11 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 11 (transLenTr ⟨72, by decide⟩ 11 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 11 (transLenTr ⟨72, by decide⟩ 11 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 11 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_11.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_12 (hp : 12 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 12 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 12 (transLenTr ⟨72, by decide⟩ 12 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 12 (transLenTr ⟨72, by decide⟩ 12 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 12 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_12.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_13 (hp : 13 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 13 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 13 (transLenTr ⟨72, by decide⟩ 13 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 13 (transLenTr ⟨72, by decide⟩ 13 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 13 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_13.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_14 (hp : 14 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 14 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 14 (transLenTr ⟨72, by decide⟩ 14 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 14 (transLenTr ⟨72, by decide⟩ 14 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 14 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_14.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_15 (hp : 15 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 15 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 15 (transLenTr ⟨72, by decide⟩ 15 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 15 (transLenTr ⟨72, by decide⟩ 15 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 15 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_15.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_16 (hp : 16 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 16 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 16 (transLenTr ⟨72, by decide⟩ 16 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 16 (transLenTr ⟨72, by decide⟩ 16 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 16 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_16.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_17 (hp : 17 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 17 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 17 (transLenTr ⟨72, by decide⟩ 17 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 17 (transLenTr ⟨72, by decide⟩ 17 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 17 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_17.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_18 (hp : 18 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 18 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 18 (transLenTr ⟨72, by decide⟩ 18 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 18 (transLenTr ⟨72, by decide⟩ 18 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 18 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_18.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_19 (hp : 19 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 19 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 19 (transLenTr ⟨72, by decide⟩ 19 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 19 (transLenTr ⟨72, by decide⟩ 19 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 19 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_19.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_20 (hp : 20 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 20 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 20 (transLenTr ⟨72, by decide⟩ 20 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 20 (transLenTr ⟨72, by decide⟩ 20 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 20 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_20.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_21 (hp : 21 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 21 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 21 (transLenTr ⟨72, by decide⟩ 21 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 21 (transLenTr ⟨72, by decide⟩ 21 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 21 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_21.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_22 (hp : 22 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 22 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 22 (transLenTr ⟨72, by decide⟩ 22 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 22 (transLenTr ⟨72, by decide⟩ 22 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 22 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_22.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_23 (hp : 23 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 23 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 23 (transLenTr ⟨72, by decide⟩ 23 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 23 (transLenTr ⟨72, by decide⟩ 23 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 23 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_23.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_72_72_24 (hp : 24 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 72 []).length)
    (hq : (normIsRep.getD 72 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 24 hp)
        (rowE2 (⟨72, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 24 (transLenTr ⟨72, by decide⟩ 24 hp))
        (rowE1 (⟨72, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨72, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨72, by decide⟩ (listedAt ⟨72, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 24 (transLenTr ⟨72, by decide⟩ 24 hp)) T72_72
      hfix72_72 hinj72_72 hcardT72_72
      (fun i => conj_mem_of_fixedPoints _ _ (T72_72 i) (hfix72_72 i) _)
      ⟨72, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨72, by decide⟩ (Q2.listedAt ⟨72, by decide⟩
        (alnCheck_rep ⟨72, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 24 hp) Q2.T72_72_2 Q2.hfix72_72_2 Q2.hinj72_72_2
      Q2.hcardT72_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T72_72_2 i) (Q2.hfix72_72_2 i) _)
      colCert_72_72_24.hD ?_).symm
  rw [alnId_72 j hj]


theorem leaf_73_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T73_6
      hfix73_6 hinj73_6 hcardT73_6
      (fun i => conj_mem_of_fixedPoints _ _ (T73_6 i) (hfix73_6 i) _)
      ⟨73, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T73_6_2 Q2.hfix73_6_2 Q2.hinj73_6_2
      Q2.hcardT73_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_6_2 i) (Q2.hfix73_6_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp) : ↥(reps ⟨6, by decide⟩)) : Coordinate 1)
        T73_6 = colFn colCert_73_6_0.D (m := 25) from colCert_73_6_0.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨6, by decide⟩ 0 hp : ↥(Q2.reps ⟨6, by decide⟩)) : Coordinate 2)
        Q2.T73_6_2 = colFn colCert_73_6_0.D (m := 25) from colCert_73_6_0.bind2]
  exact alnAll_73_6_0 j hj hq

theorem leaf_73_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T73_6
      hfix73_6 hinj73_6 hcardT73_6
      (fun i => conj_mem_of_fixedPoints _ _ (T73_6 i) (hfix73_6 i) _)
      ⟨73, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T73_6_2 Q2.hfix73_6_2 Q2.hinj73_6_2
      Q2.hcardT73_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_6_2 i) (Q2.hfix73_6_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp) : ↥(reps ⟨6, by decide⟩)) : Coordinate 1)
        T73_6 = colFn colCert_73_6_1.D (m := 25) from colCert_73_6_1.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨6, by decide⟩ 1 hp : ↥(Q2.reps ⟨6, by decide⟩)) : Coordinate 2)
        Q2.T73_6_2 = colFn colCert_73_6_1.D (m := 25) from colCert_73_6_1.bind2]
  exact alnAll_73_6_1 j hj hq

theorem leaf_73_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T73_6
      hfix73_6 hinj73_6 hcardT73_6
      (fun i => conj_mem_of_fixedPoints _ _ (T73_6 i) (hfix73_6 i) _)
      ⟨73, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T73_6_2 Q2.hfix73_6_2 Q2.hinj73_6_2
      Q2.hcardT73_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_6_2 i) (Q2.hfix73_6_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp) : ↥(reps ⟨6, by decide⟩)) : Coordinate 1)
        T73_6 = colFn colCert_73_6_2.D (m := 25) from colCert_73_6_2.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨6, by decide⟩ 2 hp : ↥(Q2.reps ⟨6, by decide⟩)) : Coordinate 2)
        Q2.T73_6_2 = colFn colCert_73_6_2.D (m := 25) from colCert_73_6_2.bind2]
  exact alnAll_73_6_2 j hj hq

theorem leaf_73_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T73_6
      hfix73_6 hinj73_6 hcardT73_6
      (fun i => conj_mem_of_fixedPoints _ _ (T73_6 i) (hfix73_6 i) _)
      ⟨73, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T73_6_2 Q2.hfix73_6_2 Q2.hinj73_6_2
      Q2.hcardT73_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_6_2 i) (Q2.hfix73_6_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp) : ↥(reps ⟨6, by decide⟩)) : Coordinate 1)
        T73_6 = colFn colCert_73_6_3.D (m := 25) from colCert_73_6_3.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨6, by decide⟩ 3 hp : ↥(Q2.reps ⟨6, by decide⟩)) : Coordinate 2)
        Q2.T73_6_2 = colFn colCert_73_6_3.D (m := 25) from colCert_73_6_3.bind2]
  exact alnAll_73_6_3 j hj hq

theorem leaf_73_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T73_6
      hfix73_6 hinj73_6 hcardT73_6
      (fun i => conj_mem_of_fixedPoints _ _ (T73_6 i) (hfix73_6 i) _)
      ⟨73, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T73_6_2 Q2.hfix73_6_2 Q2.hinj73_6_2
      Q2.hcardT73_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_6_2 i) (Q2.hfix73_6_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp) : ↥(reps ⟨6, by decide⟩)) : Coordinate 1)
        T73_6 = colFn colCert_73_6_4.D (m := 25) from colCert_73_6_4.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨6, by decide⟩ 4 hp : ↥(Q2.reps ⟨6, by decide⟩)) : Coordinate 2)
        Q2.T73_6_2 = colFn colCert_73_6_4.D (m := 25) from colCert_73_6_4.bind2]
  exact alnAll_73_6_4 j hj hq

theorem leaf_73_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T73_12
      hfix73_12 hinj73_12 hcardT73_12
      (fun i => conj_mem_of_fixedPoints _ _ (T73_12 i) (hfix73_12 i) _)
      ⟨73, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T73_12_2 Q2.hfix73_12_2 Q2.hinj73_12_2
      Q2.hcardT73_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_12_2 i) (Q2.hfix73_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T73_12 = colFn colCert_73_12_0.D (m := 25) from colCert_73_12_0.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T73_12_2 = colFn colCert_73_12_0.D (m := 25) from colCert_73_12_0.bind2]
  exact alnAll_73_12_0 j hj hq

theorem leaf_73_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T73_12
      hfix73_12 hinj73_12 hcardT73_12
      (fun i => conj_mem_of_fixedPoints _ _ (T73_12 i) (hfix73_12 i) _)
      ⟨73, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T73_12_2 Q2.hfix73_12_2 Q2.hinj73_12_2
      Q2.hcardT73_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_12_2 i) (Q2.hfix73_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T73_12 = colFn colCert_73_12_1.D (m := 25) from colCert_73_12_1.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T73_12_2 = colFn colCert_73_12_1.D (m := 25) from colCert_73_12_1.bind2]
  exact alnAll_73_12_1 j hj hq

theorem leaf_73_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T73_12
      hfix73_12 hinj73_12 hcardT73_12
      (fun i => conj_mem_of_fixedPoints _ _ (T73_12 i) (hfix73_12 i) _)
      ⟨73, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T73_12_2 Q2.hfix73_12_2 Q2.hinj73_12_2
      Q2.hcardT73_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_12_2 i) (Q2.hfix73_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T73_12 = colFn colCert_73_12_2.D (m := 25) from colCert_73_12_2.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T73_12_2 = colFn colCert_73_12_2.D (m := 25) from colCert_73_12_2.bind2]
  exact alnAll_73_12_2 j hj hq

theorem leaf_73_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T73_12
      hfix73_12 hinj73_12 hcardT73_12
      (fun i => conj_mem_of_fixedPoints _ _ (T73_12 i) (hfix73_12 i) _)
      ⟨73, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T73_12_2 Q2.hfix73_12_2 Q2.hinj73_12_2
      Q2.hcardT73_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_12_2 i) (Q2.hfix73_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T73_12 = colFn colCert_73_12_3.D (m := 25) from colCert_73_12_3.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T73_12_2 = colFn colCert_73_12_3.D (m := 25) from colCert_73_12_3.bind2]
  exact alnAll_73_12_3 j hj hq

theorem leaf_73_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T73_12
      hfix73_12 hinj73_12 hcardT73_12
      (fun i => conj_mem_of_fixedPoints _ _ (T73_12 i) (hfix73_12 i) _)
      ⟨73, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T73_12_2 Q2.hfix73_12_2 Q2.hinj73_12_2
      Q2.hcardT73_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_12_2 i) (Q2.hfix73_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T73_12 = colFn colCert_73_12_4.D (m := 25) from colCert_73_12_4.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T73_12_2 = colFn colCert_73_12_4.D (m := 25) from colCert_73_12_4.bind2]
  exact alnAll_73_12_4 j hj hq

theorem leaf_73_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T73_24
      hfix73_24 hinj73_24 hcardT73_24
      (fun i => conj_mem_of_fixedPoints _ _ (T73_24 i) (hfix73_24 i) _)
      ⟨73, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T73_24_2 Q2.hfix73_24_2 Q2.hinj73_24_2
      Q2.hcardT73_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_24_2 i) (Q2.hfix73_24_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp) : ↥(reps ⟨24, by decide⟩)) : Coordinate 1)
        T73_24 = colFn colCert_73_24_0.D (m := 25) from colCert_73_24_0.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨24, by decide⟩ 0 hp : ↥(Q2.reps ⟨24, by decide⟩)) : Coordinate 2)
        Q2.T73_24_2 = colFn colCert_73_24_0.D (m := 25) from colCert_73_24_0.bind2]
  exact alnAll_73_24_0 j hj hq

theorem leaf_73_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T73_24
      hfix73_24 hinj73_24 hcardT73_24
      (fun i => conj_mem_of_fixedPoints _ _ (T73_24 i) (hfix73_24 i) _)
      ⟨73, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T73_24_2 Q2.hfix73_24_2 Q2.hinj73_24_2
      Q2.hcardT73_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_24_2 i) (Q2.hfix73_24_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp) : ↥(reps ⟨24, by decide⟩)) : Coordinate 1)
        T73_24 = colFn colCert_73_24_1.D (m := 25) from colCert_73_24_1.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨24, by decide⟩ 1 hp : ↥(Q2.reps ⟨24, by decide⟩)) : Coordinate 2)
        Q2.T73_24_2 = colFn colCert_73_24_1.D (m := 25) from colCert_73_24_1.bind2]
  exact alnAll_73_24_1 j hj hq

theorem leaf_73_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T73_24
      hfix73_24 hinj73_24 hcardT73_24
      (fun i => conj_mem_of_fixedPoints _ _ (T73_24 i) (hfix73_24 i) _)
      ⟨73, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T73_24_2 Q2.hfix73_24_2 Q2.hinj73_24_2
      Q2.hcardT73_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_24_2 i) (Q2.hfix73_24_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp) : ↥(reps ⟨24, by decide⟩)) : Coordinate 1)
        T73_24 = colFn colCert_73_24_2.D (m := 25) from colCert_73_24_2.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨24, by decide⟩ 2 hp : ↥(Q2.reps ⟨24, by decide⟩)) : Coordinate 2)
        Q2.T73_24_2 = colFn colCert_73_24_2.D (m := 25) from colCert_73_24_2.bind2]
  exact alnAll_73_24_2 j hj hq

theorem leaf_73_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T73_24
      hfix73_24 hinj73_24 hcardT73_24
      (fun i => conj_mem_of_fixedPoints _ _ (T73_24 i) (hfix73_24 i) _)
      ⟨73, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T73_24_2 Q2.hfix73_24_2 Q2.hinj73_24_2
      Q2.hcardT73_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_24_2 i) (Q2.hfix73_24_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp) : ↥(reps ⟨24, by decide⟩)) : Coordinate 1)
        T73_24 = colFn colCert_73_24_3.D (m := 25) from colCert_73_24_3.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨24, by decide⟩ 3 hp : ↥(Q2.reps ⟨24, by decide⟩)) : Coordinate 2)
        Q2.T73_24_2 = colFn colCert_73_24_3.D (m := 25) from colCert_73_24_3.bind2]
  exact alnAll_73_24_3 j hj hq

theorem leaf_73_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T73_24
      hfix73_24 hinj73_24 hcardT73_24
      (fun i => conj_mem_of_fixedPoints _ _ (T73_24 i) (hfix73_24 i) _)
      ⟨73, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T73_24_2 Q2.hfix73_24_2 Q2.hinj73_24_2
      Q2.hcardT73_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_24_2 i) (Q2.hfix73_24_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp) : ↥(reps ⟨24, by decide⟩)) : Coordinate 1)
        T73_24 = colFn colCert_73_24_4.D (m := 25) from colCert_73_24_4.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨24, by decide⟩ 4 hp : ↥(Q2.reps ⟨24, by decide⟩)) : Coordinate 2)
        Q2.T73_24_2 = colFn colCert_73_24_4.D (m := 25) from colCert_73_24_4.bind2]
  exact alnAll_73_24_4 j hj hq

theorem leaf_73_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T73_24
      hfix73_24 hinj73_24 hcardT73_24
      (fun i => conj_mem_of_fixedPoints _ _ (T73_24 i) (hfix73_24 i) _)
      ⟨73, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T73_24_2 Q2.hfix73_24_2 Q2.hinj73_24_2
      Q2.hcardT73_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_24_2 i) (Q2.hfix73_24_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp) : ↥(reps ⟨24, by decide⟩)) : Coordinate 1)
        T73_24 = colFn colCert_73_24_5.D (m := 25) from colCert_73_24_5.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨24, by decide⟩ 5 hp : ↥(Q2.reps ⟨24, by decide⟩)) : Coordinate 2)
        Q2.T73_24_2 = colFn colCert_73_24_5.D (m := 25) from colCert_73_24_5.bind2]
  exact alnAll_73_24_5 j hj hq

theorem leaf_73_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T73_24
      hfix73_24 hinj73_24 hcardT73_24
      (fun i => conj_mem_of_fixedPoints _ _ (T73_24 i) (hfix73_24 i) _)
      ⟨73, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T73_24_2 Q2.hfix73_24_2 Q2.hinj73_24_2
      Q2.hcardT73_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_24_2 i) (Q2.hfix73_24_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp) : ↥(reps ⟨24, by decide⟩)) : Coordinate 1)
        T73_24 = colFn colCert_73_24_10.D (m := 25) from colCert_73_24_10.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨24, by decide⟩ 10 hp : ↥(Q2.reps ⟨24, by decide⟩)) : Coordinate 2)
        Q2.T73_24_2 = colFn colCert_73_24_10.D (m := 25) from colCert_73_24_10.bind2]
  exact alnAll_73_24_10 j hj hq

theorem leaf_73_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T73_24
      hfix73_24 hinj73_24 hcardT73_24
      (fun i => conj_mem_of_fixedPoints _ _ (T73_24 i) (hfix73_24 i) _)
      ⟨73, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T73_24_2 Q2.hfix73_24_2 Q2.hinj73_24_2
      Q2.hcardT73_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_24_2 i) (Q2.hfix73_24_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp) : ↥(reps ⟨24, by decide⟩)) : Coordinate 1)
        T73_24 = colFn colCert_73_24_15.D (m := 25) from colCert_73_24_15.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨24, by decide⟩ 15 hp : ↥(Q2.reps ⟨24, by decide⟩)) : Coordinate 2)
        Q2.T73_24_2 = colFn colCert_73_24_15.D (m := 25) from colCert_73_24_15.bind2]
  exact alnAll_73_24_15 j hj hq

theorem leaf_73_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T73_24
      hfix73_24 hinj73_24 hcardT73_24
      (fun i => conj_mem_of_fixedPoints _ _ (T73_24 i) (hfix73_24 i) _)
      ⟨73, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T73_24_2 Q2.hfix73_24_2 Q2.hinj73_24_2
      Q2.hcardT73_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_24_2 i) (Q2.hfix73_24_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp) : ↥(reps ⟨24, by decide⟩)) : Coordinate 1)
        T73_24 = colFn colCert_73_24_20.D (m := 25) from colCert_73_24_20.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨24, by decide⟩ 20 hp : ↥(Q2.reps ⟨24, by decide⟩)) : Coordinate 2)
        Q2.T73_24_2 = colFn colCert_73_24_20.D (m := 25) from colCert_73_24_20.bind2]
  exact alnAll_73_24_20 j hj hq

theorem leaf_73_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T73_31
      hfix73_31 hinj73_31 hcardT73_31
      (fun i => conj_mem_of_fixedPoints _ _ (T73_31 i) (hfix73_31 i) _)
      ⟨73, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T73_31_2 Q2.hfix73_31_2 Q2.hinj73_31_2
      Q2.hcardT73_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_31_2 i) (Q2.hfix73_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T73_31 = colFn colCert_73_31_0.D (m := 5) from colCert_73_31_0.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 0 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T73_31_2 = colFn colCert_73_31_0.D (m := 5) from colCert_73_31_0.bind2]
  exact alnAll_73_31_0 j hj hq

theorem leaf_73_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T73_31
      hfix73_31 hinj73_31 hcardT73_31
      (fun i => conj_mem_of_fixedPoints _ _ (T73_31 i) (hfix73_31 i) _)
      ⟨73, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T73_31_2 Q2.hfix73_31_2 Q2.hinj73_31_2
      Q2.hcardT73_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_31_2 i) (Q2.hfix73_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T73_31 = colFn colCert_73_31_1.D (m := 5) from colCert_73_31_1.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 1 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T73_31_2 = colFn colCert_73_31_1.D (m := 5) from colCert_73_31_1.bind2]
  exact alnAll_73_31_1 j hj hq

theorem leaf_73_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T73_31
      hfix73_31 hinj73_31 hcardT73_31
      (fun i => conj_mem_of_fixedPoints _ _ (T73_31 i) (hfix73_31 i) _)
      ⟨73, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T73_31_2 Q2.hfix73_31_2 Q2.hinj73_31_2
      Q2.hcardT73_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_31_2 i) (Q2.hfix73_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T73_31 = colFn colCert_73_31_2.D (m := 5) from colCert_73_31_2.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 2 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T73_31_2 = colFn colCert_73_31_2.D (m := 5) from colCert_73_31_2.bind2]
  exact alnAll_73_31_2 j hj hq

theorem leaf_73_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T73_31
      hfix73_31 hinj73_31 hcardT73_31
      (fun i => conj_mem_of_fixedPoints _ _ (T73_31 i) (hfix73_31 i) _)
      ⟨73, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T73_31_2 Q2.hfix73_31_2 Q2.hinj73_31_2
      Q2.hcardT73_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_31_2 i) (Q2.hfix73_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T73_31 = colFn colCert_73_31_3.D (m := 5) from colCert_73_31_3.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 3 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T73_31_2 = colFn colCert_73_31_3.D (m := 5) from colCert_73_31_3.bind2]
  exact alnAll_73_31_3 j hj hq

theorem leaf_73_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T73_31
      hfix73_31 hinj73_31 hcardT73_31
      (fun i => conj_mem_of_fixedPoints _ _ (T73_31 i) (hfix73_31 i) _)
      ⟨73, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T73_31_2 Q2.hfix73_31_2 Q2.hinj73_31_2
      Q2.hcardT73_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_31_2 i) (Q2.hfix73_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T73_31 = colFn colCert_73_31_4.D (m := 5) from colCert_73_31_4.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 4 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T73_31_2 = colFn colCert_73_31_4.D (m := 5) from colCert_73_31_4.bind2]
  exact alnAll_73_31_4 j hj hq

theorem leaf_73_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T73_31
      hfix73_31 hinj73_31 hcardT73_31
      (fun i => conj_mem_of_fixedPoints _ _ (T73_31 i) (hfix73_31 i) _)
      ⟨73, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T73_31_2 Q2.hfix73_31_2 Q2.hinj73_31_2
      Q2.hcardT73_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_31_2 i) (Q2.hfix73_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T73_31 = colFn colCertDiv_73_31_5.D1 (m := 5) from colCertDiv_73_31_5.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 5 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T73_31_2 = colFn colCertDiv_73_31_5.D2 (m := 5) from colCertDiv_73_31_5.bind2]
  exact alnAll_73_31_5 j hj hq

theorem leaf_73_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T73_31
      hfix73_31 hinj73_31 hcardT73_31
      (fun i => conj_mem_of_fixedPoints _ _ (T73_31 i) (hfix73_31 i) _)
      ⟨73, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T73_31_2 Q2.hfix73_31_2 Q2.hinj73_31_2
      Q2.hcardT73_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_31_2 i) (Q2.hfix73_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T73_31 = colFn colCertDiv_73_31_10.D1 (m := 5) from colCertDiv_73_31_10.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 10 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T73_31_2 = colFn colCertDiv_73_31_10.D2 (m := 5) from colCertDiv_73_31_10.bind2]
  exact alnAll_73_31_10 j hj hq

theorem leaf_73_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T73_31
      hfix73_31 hinj73_31 hcardT73_31
      (fun i => conj_mem_of_fixedPoints _ _ (T73_31 i) (hfix73_31 i) _)
      ⟨73, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T73_31_2 Q2.hfix73_31_2 Q2.hinj73_31_2
      Q2.hcardT73_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_31_2 i) (Q2.hfix73_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T73_31 = colFn colCertDiv_73_31_15.D1 (m := 5) from colCertDiv_73_31_15.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T73_31_2 = colFn colCertDiv_73_31_15.D2 (m := 5) from colCertDiv_73_31_15.bind2]
  exact alnAll_73_31_15 j hj hq

theorem leaf_73_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T73_31
      hfix73_31 hinj73_31 hcardT73_31
      (fun i => conj_mem_of_fixedPoints _ _ (T73_31 i) (hfix73_31 i) _)
      ⟨73, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T73_31_2 Q2.hfix73_31_2 Q2.hinj73_31_2
      Q2.hcardT73_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_31_2 i) (Q2.hfix73_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T73_31 = colFn colCertDiv_73_31_20.D1 (m := 5) from colCertDiv_73_31_20.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 20 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T73_31_2 = colFn colCertDiv_73_31_20.D2 (m := 5) from colCertDiv_73_31_20.bind2]
  exact alnAll_73_31_20 j hj hq

theorem leaf_73_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T73_36
      hfix73_36 hinj73_36 hcardT73_36
      (fun i => conj_mem_of_fixedPoints _ _ (T73_36 i) (hfix73_36 i) _)
      ⟨73, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T73_36_2 Q2.hfix73_36_2 Q2.hinj73_36_2
      Q2.hcardT73_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_36_2 i) (Q2.hfix73_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T73_36 = colFn colCert_73_36_0.D (m := 5) from colCert_73_36_0.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 0 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T73_36_2 = colFn colCert_73_36_0.D (m := 5) from colCert_73_36_0.bind2]
  exact alnAll_73_36_0 j hj hq

theorem leaf_73_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T73_36
      hfix73_36 hinj73_36 hcardT73_36
      (fun i => conj_mem_of_fixedPoints _ _ (T73_36 i) (hfix73_36 i) _)
      ⟨73, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T73_36_2 Q2.hfix73_36_2 Q2.hinj73_36_2
      Q2.hcardT73_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_36_2 i) (Q2.hfix73_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T73_36 = colFn colCert_73_36_1.D (m := 5) from colCert_73_36_1.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 1 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T73_36_2 = colFn colCert_73_36_1.D (m := 5) from colCert_73_36_1.bind2]
  exact alnAll_73_36_1 j hj hq

theorem leaf_73_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T73_36
      hfix73_36 hinj73_36 hcardT73_36
      (fun i => conj_mem_of_fixedPoints _ _ (T73_36 i) (hfix73_36 i) _)
      ⟨73, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T73_36_2 Q2.hfix73_36_2 Q2.hinj73_36_2
      Q2.hcardT73_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_36_2 i) (Q2.hfix73_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T73_36 = colFn colCert_73_36_2.D (m := 5) from colCert_73_36_2.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 2 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T73_36_2 = colFn colCert_73_36_2.D (m := 5) from colCert_73_36_2.bind2]
  exact alnAll_73_36_2 j hj hq

theorem leaf_73_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T73_36
      hfix73_36 hinj73_36 hcardT73_36
      (fun i => conj_mem_of_fixedPoints _ _ (T73_36 i) (hfix73_36 i) _)
      ⟨73, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T73_36_2 Q2.hfix73_36_2 Q2.hinj73_36_2
      Q2.hcardT73_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_36_2 i) (Q2.hfix73_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T73_36 = colFn colCert_73_36_3.D (m := 5) from colCert_73_36_3.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 3 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T73_36_2 = colFn colCert_73_36_3.D (m := 5) from colCert_73_36_3.bind2]
  exact alnAll_73_36_3 j hj hq

theorem leaf_73_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T73_36
      hfix73_36 hinj73_36 hcardT73_36
      (fun i => conj_mem_of_fixedPoints _ _ (T73_36 i) (hfix73_36 i) _)
      ⟨73, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T73_36_2 Q2.hfix73_36_2 Q2.hinj73_36_2
      Q2.hcardT73_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_36_2 i) (Q2.hfix73_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T73_36 = colFn colCert_73_36_4.D (m := 5) from colCert_73_36_4.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 4 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T73_36_2 = colFn colCert_73_36_4.D (m := 5) from colCert_73_36_4.bind2]
  exact alnAll_73_36_4 j hj hq

theorem leaf_73_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T73_36
      hfix73_36 hinj73_36 hcardT73_36
      (fun i => conj_mem_of_fixedPoints _ _ (T73_36 i) (hfix73_36 i) _)
      ⟨73, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T73_36_2 Q2.hfix73_36_2 Q2.hinj73_36_2
      Q2.hcardT73_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_36_2 i) (Q2.hfix73_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T73_36 = colFn colCertDiv_73_36_5.D1 (m := 5) from colCertDiv_73_36_5.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T73_36_2 = colFn colCertDiv_73_36_5.D2 (m := 5) from colCertDiv_73_36_5.bind2]
  exact alnAll_73_36_5 j hj hq

theorem leaf_73_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T73_36
      hfix73_36 hinj73_36 hcardT73_36
      (fun i => conj_mem_of_fixedPoints _ _ (T73_36 i) (hfix73_36 i) _)
      ⟨73, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T73_36_2 Q2.hfix73_36_2 Q2.hinj73_36_2
      Q2.hcardT73_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_36_2 i) (Q2.hfix73_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T73_36 = colFn colCertDiv_73_36_10.D1 (m := 5) from colCertDiv_73_36_10.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T73_36_2 = colFn colCertDiv_73_36_10.D2 (m := 5) from colCertDiv_73_36_10.bind2]
  exact alnAll_73_36_10 j hj hq

theorem leaf_73_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T73_36
      hfix73_36 hinj73_36 hcardT73_36
      (fun i => conj_mem_of_fixedPoints _ _ (T73_36 i) (hfix73_36 i) _)
      ⟨73, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T73_36_2 Q2.hfix73_36_2 Q2.hinj73_36_2
      Q2.hcardT73_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_36_2 i) (Q2.hfix73_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T73_36 = colFn colCertDiv_73_36_15.D1 (m := 5) from colCertDiv_73_36_15.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 15 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T73_36_2 = colFn colCertDiv_73_36_15.D2 (m := 5) from colCertDiv_73_36_15.bind2]
  exact alnAll_73_36_15 j hj hq

theorem leaf_73_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T73_36
      hfix73_36 hinj73_36 hcardT73_36
      (fun i => conj_mem_of_fixedPoints _ _ (T73_36 i) (hfix73_36 i) _)
      ⟨73, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T73_36_2 Q2.hfix73_36_2 Q2.hinj73_36_2
      Q2.hcardT73_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_36_2 i) (Q2.hfix73_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T73_36 = colFn colCertDiv_73_36_20.D1 (m := 5) from colCertDiv_73_36_20.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T73_36_2 = colFn colCertDiv_73_36_20.D2 (m := 5) from colCertDiv_73_36_20.bind2]
  exact alnAll_73_36_20 j hj hq

theorem leaf_73_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T73_41
      hfix73_41 hinj73_41 hcardT73_41
      (fun i => conj_mem_of_fixedPoints _ _ (T73_41 i) (hfix73_41 i) _)
      ⟨73, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T73_41_2 Q2.hfix73_41_2 Q2.hinj73_41_2
      Q2.hcardT73_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_41_2 i) (Q2.hfix73_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T73_41 = colFn colCert_73_41_0.D (m := 5) from colCert_73_41_0.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 0 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T73_41_2 = colFn colCert_73_41_0.D (m := 5) from colCert_73_41_0.bind2]
  exact alnAll_73_41_0 j hj hq

theorem leaf_73_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T73_41
      hfix73_41 hinj73_41 hcardT73_41
      (fun i => conj_mem_of_fixedPoints _ _ (T73_41 i) (hfix73_41 i) _)
      ⟨73, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T73_41_2 Q2.hfix73_41_2 Q2.hinj73_41_2
      Q2.hcardT73_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_41_2 i) (Q2.hfix73_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T73_41 = colFn colCert_73_41_1.D (m := 5) from colCert_73_41_1.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 1 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T73_41_2 = colFn colCert_73_41_1.D (m := 5) from colCert_73_41_1.bind2]
  exact alnAll_73_41_1 j hj hq

theorem leaf_73_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T73_41
      hfix73_41 hinj73_41 hcardT73_41
      (fun i => conj_mem_of_fixedPoints _ _ (T73_41 i) (hfix73_41 i) _)
      ⟨73, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T73_41_2 Q2.hfix73_41_2 Q2.hinj73_41_2
      Q2.hcardT73_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_41_2 i) (Q2.hfix73_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T73_41 = colFn colCert_73_41_2.D (m := 5) from colCert_73_41_2.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 2 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T73_41_2 = colFn colCert_73_41_2.D (m := 5) from colCert_73_41_2.bind2]
  exact alnAll_73_41_2 j hj hq

theorem leaf_73_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T73_41
      hfix73_41 hinj73_41 hcardT73_41
      (fun i => conj_mem_of_fixedPoints _ _ (T73_41 i) (hfix73_41 i) _)
      ⟨73, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T73_41_2 Q2.hfix73_41_2 Q2.hinj73_41_2
      Q2.hcardT73_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_41_2 i) (Q2.hfix73_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T73_41 = colFn colCert_73_41_3.D (m := 5) from colCert_73_41_3.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 3 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T73_41_2 = colFn colCert_73_41_3.D (m := 5) from colCert_73_41_3.bind2]
  exact alnAll_73_41_3 j hj hq

theorem leaf_73_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T73_41
      hfix73_41 hinj73_41 hcardT73_41
      (fun i => conj_mem_of_fixedPoints _ _ (T73_41 i) (hfix73_41 i) _)
      ⟨73, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T73_41_2 Q2.hfix73_41_2 Q2.hinj73_41_2
      Q2.hcardT73_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_41_2 i) (Q2.hfix73_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T73_41 = colFn colCert_73_41_4.D (m := 5) from colCert_73_41_4.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 4 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T73_41_2 = colFn colCert_73_41_4.D (m := 5) from colCert_73_41_4.bind2]
  exact alnAll_73_41_4 j hj hq

theorem leaf_73_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T73_41
      hfix73_41 hinj73_41 hcardT73_41
      (fun i => conj_mem_of_fixedPoints _ _ (T73_41 i) (hfix73_41 i) _)
      ⟨73, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T73_41_2 Q2.hfix73_41_2 Q2.hinj73_41_2
      Q2.hcardT73_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_41_2 i) (Q2.hfix73_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T73_41 = colFn colCertDiv_73_41_5.D1 (m := 5) from colCertDiv_73_41_5.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T73_41_2 = colFn colCertDiv_73_41_5.D2 (m := 5) from colCertDiv_73_41_5.bind2]
  exact alnAll_73_41_5 j hj hq

theorem leaf_73_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T73_41
      hfix73_41 hinj73_41 hcardT73_41
      (fun i => conj_mem_of_fixedPoints _ _ (T73_41 i) (hfix73_41 i) _)
      ⟨73, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T73_41_2 Q2.hfix73_41_2 Q2.hinj73_41_2
      Q2.hcardT73_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_41_2 i) (Q2.hfix73_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T73_41 = colFn colCertDiv_73_41_10.D1 (m := 5) from colCertDiv_73_41_10.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T73_41_2 = colFn colCertDiv_73_41_10.D2 (m := 5) from colCertDiv_73_41_10.bind2]
  exact alnAll_73_41_10 j hj hq

theorem leaf_73_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T73_41
      hfix73_41 hinj73_41 hcardT73_41
      (fun i => conj_mem_of_fixedPoints _ _ (T73_41 i) (hfix73_41 i) _)
      ⟨73, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T73_41_2 Q2.hfix73_41_2 Q2.hinj73_41_2
      Q2.hcardT73_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_41_2 i) (Q2.hfix73_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T73_41 = colFn colCertDiv_73_41_15.D1 (m := 5) from colCertDiv_73_41_15.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 15 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T73_41_2 = colFn colCertDiv_73_41_15.D2 (m := 5) from colCertDiv_73_41_15.bind2]
  exact alnAll_73_41_15 j hj hq

theorem leaf_73_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T73_41
      hfix73_41 hinj73_41 hcardT73_41
      (fun i => conj_mem_of_fixedPoints _ _ (T73_41 i) (hfix73_41 i) _)
      ⟨73, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T73_41_2 Q2.hfix73_41_2 Q2.hinj73_41_2
      Q2.hcardT73_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_41_2 i) (Q2.hfix73_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T73_41 = colFn colCertDiv_73_41_20.D1 (m := 5) from colCertDiv_73_41_20.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T73_41_2 = colFn colCertDiv_73_41_20.D2 (m := 5) from colCertDiv_73_41_20.bind2]
  exact alnAll_73_41_20 j hj hq

theorem leaf_73_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T73_46
      hfix73_46 hinj73_46 hcardT73_46
      (fun i => conj_mem_of_fixedPoints _ _ (T73_46 i) (hfix73_46 i) _)
      ⟨73, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T73_46_2 Q2.hfix73_46_2 Q2.hinj73_46_2
      Q2.hcardT73_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_46_2 i) (Q2.hfix73_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T73_46 = colFn colCert_73_46_0.D (m := 5) from colCert_73_46_0.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 0 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T73_46_2 = colFn colCert_73_46_0.D (m := 5) from colCert_73_46_0.bind2]
  exact alnAll_73_46_0 j hj hq

theorem leaf_73_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T73_46
      hfix73_46 hinj73_46 hcardT73_46
      (fun i => conj_mem_of_fixedPoints _ _ (T73_46 i) (hfix73_46 i) _)
      ⟨73, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T73_46_2 Q2.hfix73_46_2 Q2.hinj73_46_2
      Q2.hcardT73_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_46_2 i) (Q2.hfix73_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T73_46 = colFn colCert_73_46_1.D (m := 5) from colCert_73_46_1.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 1 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T73_46_2 = colFn colCert_73_46_1.D (m := 5) from colCert_73_46_1.bind2]
  exact alnAll_73_46_1 j hj hq

theorem leaf_73_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T73_46
      hfix73_46 hinj73_46 hcardT73_46
      (fun i => conj_mem_of_fixedPoints _ _ (T73_46 i) (hfix73_46 i) _)
      ⟨73, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T73_46_2 Q2.hfix73_46_2 Q2.hinj73_46_2
      Q2.hcardT73_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_46_2 i) (Q2.hfix73_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T73_46 = colFn colCert_73_46_2.D (m := 5) from colCert_73_46_2.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 2 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T73_46_2 = colFn colCert_73_46_2.D (m := 5) from colCert_73_46_2.bind2]
  exact alnAll_73_46_2 j hj hq

theorem leaf_73_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T73_46
      hfix73_46 hinj73_46 hcardT73_46
      (fun i => conj_mem_of_fixedPoints _ _ (T73_46 i) (hfix73_46 i) _)
      ⟨73, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T73_46_2 Q2.hfix73_46_2 Q2.hinj73_46_2
      Q2.hcardT73_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_46_2 i) (Q2.hfix73_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T73_46 = colFn colCert_73_46_3.D (m := 5) from colCert_73_46_3.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 3 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T73_46_2 = colFn colCert_73_46_3.D (m := 5) from colCert_73_46_3.bind2]
  exact alnAll_73_46_3 j hj hq

theorem leaf_73_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T73_46
      hfix73_46 hinj73_46 hcardT73_46
      (fun i => conj_mem_of_fixedPoints _ _ (T73_46 i) (hfix73_46 i) _)
      ⟨73, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T73_46_2 Q2.hfix73_46_2 Q2.hinj73_46_2
      Q2.hcardT73_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_46_2 i) (Q2.hfix73_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T73_46 = colFn colCert_73_46_4.D (m := 5) from colCert_73_46_4.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 4 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T73_46_2 = colFn colCert_73_46_4.D (m := 5) from colCert_73_46_4.bind2]
  exact alnAll_73_46_4 j hj hq

theorem leaf_73_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T73_46
      hfix73_46 hinj73_46 hcardT73_46
      (fun i => conj_mem_of_fixedPoints _ _ (T73_46 i) (hfix73_46 i) _)
      ⟨73, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T73_46_2 Q2.hfix73_46_2 Q2.hinj73_46_2
      Q2.hcardT73_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_46_2 i) (Q2.hfix73_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T73_46 = colFn colCertDiv_73_46_5.D1 (m := 5) from colCertDiv_73_46_5.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 5 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T73_46_2 = colFn colCertDiv_73_46_5.D2 (m := 5) from colCertDiv_73_46_5.bind2]
  exact alnAll_73_46_5 j hj hq

theorem leaf_73_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T73_46
      hfix73_46 hinj73_46 hcardT73_46
      (fun i => conj_mem_of_fixedPoints _ _ (T73_46 i) (hfix73_46 i) _)
      ⟨73, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T73_46_2 Q2.hfix73_46_2 Q2.hinj73_46_2
      Q2.hcardT73_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_46_2 i) (Q2.hfix73_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T73_46 = colFn colCertDiv_73_46_10.D1 (m := 5) from colCertDiv_73_46_10.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 10 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T73_46_2 = colFn colCertDiv_73_46_10.D2 (m := 5) from colCertDiv_73_46_10.bind2]
  exact alnAll_73_46_10 j hj hq

theorem leaf_73_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T73_46
      hfix73_46 hinj73_46 hcardT73_46
      (fun i => conj_mem_of_fixedPoints _ _ (T73_46 i) (hfix73_46 i) _)
      ⟨73, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T73_46_2 Q2.hfix73_46_2 Q2.hinj73_46_2
      Q2.hcardT73_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_46_2 i) (Q2.hfix73_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T73_46 = colFn colCertDiv_73_46_15.D1 (m := 5) from colCertDiv_73_46_15.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T73_46_2 = colFn colCertDiv_73_46_15.D2 (m := 5) from colCertDiv_73_46_15.bind2]
  exact alnAll_73_46_15 j hj hq

theorem leaf_73_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T73_46
      hfix73_46 hinj73_46 hcardT73_46
      (fun i => conj_mem_of_fixedPoints _ _ (T73_46 i) (hfix73_46 i) _)
      ⟨73, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T73_46_2 Q2.hfix73_46_2 Q2.hinj73_46_2
      Q2.hcardT73_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_46_2 i) (Q2.hfix73_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T73_46 = colFn colCertDiv_73_46_20.D1 (m := 5) from colCertDiv_73_46_20.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 20 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T73_46_2 = colFn colCertDiv_73_46_20.D2 (m := 5) from colCertDiv_73_46_20.bind2]
  exact alnAll_73_46_20 j hj hq

theorem leaf_73_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T73_51
      hfix73_51 hinj73_51 hcardT73_51
      (fun i => conj_mem_of_fixedPoints _ _ (T73_51 i) (hfix73_51 i) _)
      ⟨73, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T73_51_2 Q2.hfix73_51_2 Q2.hinj73_51_2
      Q2.hcardT73_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_51_2 i) (Q2.hfix73_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T73_51 = colFn colCert_73_51_0.D (m := 5) from colCert_73_51_0.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 0 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T73_51_2 = colFn colCert_73_51_0.D (m := 5) from colCert_73_51_0.bind2]
  exact alnAll_73_51_0 j hj hq

theorem leaf_73_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T73_51
      hfix73_51 hinj73_51 hcardT73_51
      (fun i => conj_mem_of_fixedPoints _ _ (T73_51 i) (hfix73_51 i) _)
      ⟨73, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T73_51_2 Q2.hfix73_51_2 Q2.hinj73_51_2
      Q2.hcardT73_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_51_2 i) (Q2.hfix73_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T73_51 = colFn colCert_73_51_1.D (m := 5) from colCert_73_51_1.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 1 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T73_51_2 = colFn colCert_73_51_1.D (m := 5) from colCert_73_51_1.bind2]
  exact alnAll_73_51_1 j hj hq

theorem leaf_73_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T73_51
      hfix73_51 hinj73_51 hcardT73_51
      (fun i => conj_mem_of_fixedPoints _ _ (T73_51 i) (hfix73_51 i) _)
      ⟨73, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T73_51_2 Q2.hfix73_51_2 Q2.hinj73_51_2
      Q2.hcardT73_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_51_2 i) (Q2.hfix73_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T73_51 = colFn colCert_73_51_2.D (m := 5) from colCert_73_51_2.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 2 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T73_51_2 = colFn colCert_73_51_2.D (m := 5) from colCert_73_51_2.bind2]
  exact alnAll_73_51_2 j hj hq

theorem leaf_73_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T73_51
      hfix73_51 hinj73_51 hcardT73_51
      (fun i => conj_mem_of_fixedPoints _ _ (T73_51 i) (hfix73_51 i) _)
      ⟨73, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T73_51_2 Q2.hfix73_51_2 Q2.hinj73_51_2
      Q2.hcardT73_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_51_2 i) (Q2.hfix73_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T73_51 = colFn colCert_73_51_3.D (m := 5) from colCert_73_51_3.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 3 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T73_51_2 = colFn colCert_73_51_3.D (m := 5) from colCert_73_51_3.bind2]
  exact alnAll_73_51_3 j hj hq

theorem leaf_73_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T73_51
      hfix73_51 hinj73_51 hcardT73_51
      (fun i => conj_mem_of_fixedPoints _ _ (T73_51 i) (hfix73_51 i) _)
      ⟨73, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T73_51_2 Q2.hfix73_51_2 Q2.hinj73_51_2
      Q2.hcardT73_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_51_2 i) (Q2.hfix73_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T73_51 = colFn colCert_73_51_4.D (m := 5) from colCert_73_51_4.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 4 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T73_51_2 = colFn colCert_73_51_4.D (m := 5) from colCert_73_51_4.bind2]
  exact alnAll_73_51_4 j hj hq

theorem leaf_73_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T73_51
      hfix73_51 hinj73_51 hcardT73_51
      (fun i => conj_mem_of_fixedPoints _ _ (T73_51 i) (hfix73_51 i) _)
      ⟨73, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T73_51_2 Q2.hfix73_51_2 Q2.hinj73_51_2
      Q2.hcardT73_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_51_2 i) (Q2.hfix73_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T73_51 = colFn colCertDiv_73_51_5.D1 (m := 5) from colCertDiv_73_51_5.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T73_51_2 = colFn colCertDiv_73_51_5.D2 (m := 5) from colCertDiv_73_51_5.bind2]
  exact alnAll_73_51_5 j hj hq

theorem leaf_73_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T73_51
      hfix73_51 hinj73_51 hcardT73_51
      (fun i => conj_mem_of_fixedPoints _ _ (T73_51 i) (hfix73_51 i) _)
      ⟨73, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T73_51_2 Q2.hfix73_51_2 Q2.hinj73_51_2
      Q2.hcardT73_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_51_2 i) (Q2.hfix73_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T73_51 = colFn colCertDiv_73_51_10.D1 (m := 5) from colCertDiv_73_51_10.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T73_51_2 = colFn colCertDiv_73_51_10.D2 (m := 5) from colCertDiv_73_51_10.bind2]
  exact alnAll_73_51_10 j hj hq

theorem leaf_73_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T73_51
      hfix73_51 hinj73_51 hcardT73_51
      (fun i => conj_mem_of_fixedPoints _ _ (T73_51 i) (hfix73_51 i) _)
      ⟨73, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T73_51_2 Q2.hfix73_51_2 Q2.hinj73_51_2
      Q2.hcardT73_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_51_2 i) (Q2.hfix73_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T73_51 = colFn colCertDiv_73_51_15.D1 (m := 5) from colCertDiv_73_51_15.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T73_51_2 = colFn colCertDiv_73_51_15.D2 (m := 5) from colCertDiv_73_51_15.bind2]
  exact alnAll_73_51_15 j hj hq

theorem leaf_73_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T73_51
      hfix73_51 hinj73_51 hcardT73_51
      (fun i => conj_mem_of_fixedPoints _ _ (T73_51 i) (hfix73_51 i) _)
      ⟨73, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T73_51_2 Q2.hfix73_51_2 Q2.hinj73_51_2
      Q2.hcardT73_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_51_2 i) (Q2.hfix73_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T73_51 = colFn colCertDiv_73_51_20.D1 (m := 5) from colCertDiv_73_51_20.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T73_51_2 = colFn colCertDiv_73_51_20.D2 (m := 5) from colCertDiv_73_51_20.bind2]
  exact alnAll_73_51_20 j hj hq

theorem leaf_73_73_0 (hp : 0 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 0 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 0 (transLenTr ⟨73, by decide⟩ 0 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 0 (transLenTr ⟨73, by decide⟩ 0 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 0 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 0 (transLenTr ⟨73, by decide⟩ 0 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_0.D (m := 5) from colCert_73_73_0.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 0 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_0.D (m := 5) from colCert_73_73_0.bind2]
  exact alnAll_73_73_0 j hj hq

theorem leaf_73_73_1 (hp : 1 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 1 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 1 (transLenTr ⟨73, by decide⟩ 1 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 1 (transLenTr ⟨73, by decide⟩ 1 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 1 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 1 (transLenTr ⟨73, by decide⟩ 1 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_1.D (m := 5) from colCert_73_73_1.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 1 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_1.D (m := 5) from colCert_73_73_1.bind2]
  exact alnAll_73_73_1 j hj hq

theorem leaf_73_73_2 (hp : 2 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 2 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 2 (transLenTr ⟨73, by decide⟩ 2 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 2 (transLenTr ⟨73, by decide⟩ 2 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 2 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 2 (transLenTr ⟨73, by decide⟩ 2 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_2.D (m := 5) from colCert_73_73_2.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 2 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_2.D (m := 5) from colCert_73_73_2.bind2]
  exact alnAll_73_73_2 j hj hq

theorem leaf_73_73_3 (hp : 3 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 3 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 3 (transLenTr ⟨73, by decide⟩ 3 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 3 (transLenTr ⟨73, by decide⟩ 3 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 3 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 3 (transLenTr ⟨73, by decide⟩ 3 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_3.D (m := 5) from colCert_73_73_3.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 3 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_3.D (m := 5) from colCert_73_73_3.bind2]
  exact alnAll_73_73_3 j hj hq

theorem leaf_73_73_4 (hp : 4 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 4 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 4 (transLenTr ⟨73, by decide⟩ 4 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 4 (transLenTr ⟨73, by decide⟩ 4 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 4 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 4 (transLenTr ⟨73, by decide⟩ 4 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_4.D (m := 5) from colCert_73_73_4.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 4 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_4.D (m := 5) from colCert_73_73_4.bind2]
  exact alnAll_73_73_4 j hj hq

theorem leaf_73_73_5 (hp : 5 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 5 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 5 (transLenTr ⟨73, by decide⟩ 5 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 5 (transLenTr ⟨73, by decide⟩ 5 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 5 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 5 (transLenTr ⟨73, by decide⟩ 5 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_5.D (m := 5) from colCert_73_73_5.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 5 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_5.D (m := 5) from colCert_73_73_5.bind2]
  exact alnAll_73_73_5 j hj hq

theorem leaf_73_73_6 (hp : 6 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 6 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 6 (transLenTr ⟨73, by decide⟩ 6 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 6 (transLenTr ⟨73, by decide⟩ 6 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 6 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 6 (transLenTr ⟨73, by decide⟩ 6 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_6.D (m := 5) from colCert_73_73_6.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 6 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_6.D (m := 5) from colCert_73_73_6.bind2]
  exact alnAll_73_73_6 j hj hq

theorem leaf_73_73_7 (hp : 7 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 7 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 7 (transLenTr ⟨73, by decide⟩ 7 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 7 (transLenTr ⟨73, by decide⟩ 7 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 7 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 7 (transLenTr ⟨73, by decide⟩ 7 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_7.D (m := 5) from colCert_73_73_7.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 7 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_7.D (m := 5) from colCert_73_73_7.bind2]
  exact alnAll_73_73_7 j hj hq

theorem leaf_73_73_8 (hp : 8 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 8 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 8 (transLenTr ⟨73, by decide⟩ 8 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 8 (transLenTr ⟨73, by decide⟩ 8 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 8 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 8 (transLenTr ⟨73, by decide⟩ 8 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_8.D (m := 5) from colCert_73_73_8.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 8 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_8.D (m := 5) from colCert_73_73_8.bind2]
  exact alnAll_73_73_8 j hj hq

theorem leaf_73_73_9 (hp : 9 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 9 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 9 (transLenTr ⟨73, by decide⟩ 9 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 9 (transLenTr ⟨73, by decide⟩ 9 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 9 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 9 (transLenTr ⟨73, by decide⟩ 9 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_9.D (m := 5) from colCert_73_73_9.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 9 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_9.D (m := 5) from colCert_73_73_9.bind2]
  exact alnAll_73_73_9 j hj hq

theorem leaf_73_73_10 (hp : 10 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 10 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 10 (transLenTr ⟨73, by decide⟩ 10 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 10 (transLenTr ⟨73, by decide⟩ 10 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 10 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 10 (transLenTr ⟨73, by decide⟩ 10 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_10.D (m := 5) from colCert_73_73_10.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 10 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_10.D (m := 5) from colCert_73_73_10.bind2]
  exact alnAll_73_73_10 j hj hq

theorem leaf_73_73_11 (hp : 11 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 11 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 11 (transLenTr ⟨73, by decide⟩ 11 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 11 (transLenTr ⟨73, by decide⟩ 11 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 11 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 11 (transLenTr ⟨73, by decide⟩ 11 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_11.D (m := 5) from colCert_73_73_11.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 11 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_11.D (m := 5) from colCert_73_73_11.bind2]
  exact alnAll_73_73_11 j hj hq

theorem leaf_73_73_12 (hp : 12 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 12 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 12 (transLenTr ⟨73, by decide⟩ 12 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 12 (transLenTr ⟨73, by decide⟩ 12 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 12 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 12 (transLenTr ⟨73, by decide⟩ 12 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_12.D (m := 5) from colCert_73_73_12.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 12 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_12.D (m := 5) from colCert_73_73_12.bind2]
  exact alnAll_73_73_12 j hj hq

theorem leaf_73_73_13 (hp : 13 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 13 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 13 (transLenTr ⟨73, by decide⟩ 13 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 13 (transLenTr ⟨73, by decide⟩ 13 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 13 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 13 (transLenTr ⟨73, by decide⟩ 13 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_13.D (m := 5) from colCert_73_73_13.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 13 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_13.D (m := 5) from colCert_73_73_13.bind2]
  exact alnAll_73_73_13 j hj hq

theorem leaf_73_73_14 (hp : 14 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 14 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 14 (transLenTr ⟨73, by decide⟩ 14 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 14 (transLenTr ⟨73, by decide⟩ 14 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 14 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 14 (transLenTr ⟨73, by decide⟩ 14 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_14.D (m := 5) from colCert_73_73_14.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 14 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_14.D (m := 5) from colCert_73_73_14.bind2]
  exact alnAll_73_73_14 j hj hq

theorem leaf_73_73_15 (hp : 15 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 15 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 15 (transLenTr ⟨73, by decide⟩ 15 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 15 (transLenTr ⟨73, by decide⟩ 15 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 15 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 15 (transLenTr ⟨73, by decide⟩ 15 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_15.D (m := 5) from colCert_73_73_15.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 15 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_15.D (m := 5) from colCert_73_73_15.bind2]
  exact alnAll_73_73_15 j hj hq

theorem leaf_73_73_16 (hp : 16 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 16 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 16 (transLenTr ⟨73, by decide⟩ 16 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 16 (transLenTr ⟨73, by decide⟩ 16 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 16 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 16 (transLenTr ⟨73, by decide⟩ 16 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_16.D (m := 5) from colCert_73_73_16.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 16 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_16.D (m := 5) from colCert_73_73_16.bind2]
  exact alnAll_73_73_16 j hj hq

theorem leaf_73_73_17 (hp : 17 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 17 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 17 (transLenTr ⟨73, by decide⟩ 17 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 17 (transLenTr ⟨73, by decide⟩ 17 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 17 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 17 (transLenTr ⟨73, by decide⟩ 17 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_17.D (m := 5) from colCert_73_73_17.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 17 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_17.D (m := 5) from colCert_73_73_17.bind2]
  exact alnAll_73_73_17 j hj hq

theorem leaf_73_73_18 (hp : 18 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 18 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 18 (transLenTr ⟨73, by decide⟩ 18 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 18 (transLenTr ⟨73, by decide⟩ 18 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 18 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 18 (transLenTr ⟨73, by decide⟩ 18 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_18.D (m := 5) from colCert_73_73_18.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 18 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_18.D (m := 5) from colCert_73_73_18.bind2]
  exact alnAll_73_73_18 j hj hq

theorem leaf_73_73_19 (hp : 19 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 19 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 19 (transLenTr ⟨73, by decide⟩ 19 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 19 (transLenTr ⟨73, by decide⟩ 19 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 19 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 19 (transLenTr ⟨73, by decide⟩ 19 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_19.D (m := 5) from colCert_73_73_19.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 19 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_19.D (m := 5) from colCert_73_73_19.bind2]
  exact alnAll_73_73_19 j hj hq

theorem leaf_73_73_20 (hp : 20 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 20 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 20 (transLenTr ⟨73, by decide⟩ 20 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 20 (transLenTr ⟨73, by decide⟩ 20 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 20 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 20 (transLenTr ⟨73, by decide⟩ 20 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_20.D (m := 5) from colCert_73_73_20.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 20 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_20.D (m := 5) from colCert_73_73_20.bind2]
  exact alnAll_73_73_20 j hj hq

theorem leaf_73_73_21 (hp : 21 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 21 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 21 (transLenTr ⟨73, by decide⟩ 21 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 21 (transLenTr ⟨73, by decide⟩ 21 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 21 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 21 (transLenTr ⟨73, by decide⟩ 21 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_21.D (m := 5) from colCert_73_73_21.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 21 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_21.D (m := 5) from colCert_73_73_21.bind2]
  exact alnAll_73_73_21 j hj hq

theorem leaf_73_73_22 (hp : 22 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 22 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 22 (transLenTr ⟨73, by decide⟩ 22 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 22 (transLenTr ⟨73, by decide⟩ 22 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 22 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 22 (transLenTr ⟨73, by decide⟩ 22 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_22.D (m := 5) from colCert_73_73_22.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 22 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_22.D (m := 5) from colCert_73_73_22.bind2]
  exact alnAll_73_73_22 j hj hq

theorem leaf_73_73_23 (hp : 23 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 23 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 23 (transLenTr ⟨73, by decide⟩ 23 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 23 (transLenTr ⟨73, by decide⟩ 23 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 23 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 23 (transLenTr ⟨73, by decide⟩ 23 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_23.D (m := 5) from colCert_73_73_23.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 23 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_23.D (m := 5) from colCert_73_73_23.bind2]
  exact alnAll_73_73_23 j hj hq

theorem leaf_73_73_24 (hp : 24 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 24 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 24 (transLenTr ⟨73, by decide⟩ 24 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 24 (transLenTr ⟨73, by decide⟩ 24 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 24 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 24 (transLenTr ⟨73, by decide⟩ 24 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_24.D (m := 5) from colCert_73_73_24.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 24 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_24.D (m := 5) from colCert_73_73_24.bind2]
  exact alnAll_73_73_24 j hj hq

theorem leaf_73_73_25 (hp : 25 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 25 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 25 (transLenTr ⟨73, by decide⟩ 25 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 25 (transLenTr ⟨73, by decide⟩ 25 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 25 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 25 (transLenTr ⟨73, by decide⟩ 25 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_25.D (m := 5) from colCert_73_73_25.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 25 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_25.D (m := 5) from colCert_73_73_25.bind2]
  exact alnAll_73_73_25 j hj hq

theorem leaf_73_73_30 (hp : 30 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 30 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 30 (transLenTr ⟨73, by decide⟩ 30 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 30 (transLenTr ⟨73, by decide⟩ 30 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 30 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 30 (transLenTr ⟨73, by decide⟩ 30 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_30.D (m := 5) from colCert_73_73_30.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 30 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_30.D (m := 5) from colCert_73_73_30.bind2]
  exact alnAll_73_73_30 j hj hq

theorem leaf_73_73_35 (hp : 35 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 35 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 35 (transLenTr ⟨73, by decide⟩ 35 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 35 (transLenTr ⟨73, by decide⟩ 35 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 35 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 35 (transLenTr ⟨73, by decide⟩ 35 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_35.D (m := 5) from colCert_73_73_35.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 35 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_35.D (m := 5) from colCert_73_73_35.bind2]
  exact alnAll_73_73_35 j hj hq

theorem leaf_73_73_40 (hp : 40 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 40 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 40 (transLenTr ⟨73, by decide⟩ 40 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 40 (transLenTr ⟨73, by decide⟩ 40 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 40 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 40 (transLenTr ⟨73, by decide⟩ 40 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_40.D (m := 5) from colCert_73_73_40.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 40 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_40.D (m := 5) from colCert_73_73_40.bind2]
  exact alnAll_73_73_40 j hj hq

theorem leaf_73_73_45 (hp : 45 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 45 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 45 (transLenTr ⟨73, by decide⟩ 45 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 45 (transLenTr ⟨73, by decide⟩ 45 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 45 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 45 (transLenTr ⟨73, by decide⟩ 45 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_45.D (m := 5) from colCert_73_73_45.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 45 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_45.D (m := 5) from colCert_73_73_45.bind2]
  exact alnAll_73_73_45 j hj hq

theorem leaf_73_73_50 (hp : 50 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 50 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 50 (transLenTr ⟨73, by decide⟩ 50 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 50 (transLenTr ⟨73, by decide⟩ 50 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 50 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 50 (transLenTr ⟨73, by decide⟩ 50 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_50.D (m := 5) from colCert_73_73_50.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 50 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_50.D (m := 5) from colCert_73_73_50.bind2]
  exact alnAll_73_73_50 j hj hq

theorem leaf_73_73_55 (hp : 55 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 55 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 55 (transLenTr ⟨73, by decide⟩ 55 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 55 (transLenTr ⟨73, by decide⟩ 55 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 55 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 55 (transLenTr ⟨73, by decide⟩ 55 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_55.D (m := 5) from colCert_73_73_55.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 55 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_55.D (m := 5) from colCert_73_73_55.bind2]
  exact alnAll_73_73_55 j hj hq

theorem leaf_73_73_60 (hp : 60 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 60 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 60 (transLenTr ⟨73, by decide⟩ 60 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 60 (transLenTr ⟨73, by decide⟩ 60 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 60 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 60 (transLenTr ⟨73, by decide⟩ 60 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_60.D (m := 5) from colCert_73_73_60.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 60 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_60.D (m := 5) from colCert_73_73_60.bind2]
  exact alnAll_73_73_60 j hj hq

theorem leaf_73_73_65 (hp : 65 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 65 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 65 (transLenTr ⟨73, by decide⟩ 65 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 65 (transLenTr ⟨73, by decide⟩ 65 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 65 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 65 (transLenTr ⟨73, by decide⟩ 65 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_65.D (m := 5) from colCert_73_73_65.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 65 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_65.D (m := 5) from colCert_73_73_65.bind2]
  exact alnAll_73_73_65 j hj hq

theorem leaf_73_73_70 (hp : 70 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 70 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 70 (transLenTr ⟨73, by decide⟩ 70 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 70 (transLenTr ⟨73, by decide⟩ 70 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 70 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 70 (transLenTr ⟨73, by decide⟩ 70 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_70.D (m := 5) from colCert_73_73_70.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 70 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_70.D (m := 5) from colCert_73_73_70.bind2]
  exact alnAll_73_73_70 j hj hq

theorem leaf_73_73_75 (hp : 75 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 75 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 75 (transLenTr ⟨73, by decide⟩ 75 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 75 (transLenTr ⟨73, by decide⟩ 75 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 75 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 75 (transLenTr ⟨73, by decide⟩ 75 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_75.D (m := 5) from colCert_73_73_75.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 75 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_75.D (m := 5) from colCert_73_73_75.bind2]
  exact alnAll_73_73_75 j hj hq

theorem leaf_73_73_80 (hp : 80 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 80 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 80 (transLenTr ⟨73, by decide⟩ 80 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 80 (transLenTr ⟨73, by decide⟩ 80 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 80 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 80 (transLenTr ⟨73, by decide⟩ 80 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_80.D (m := 5) from colCert_73_73_80.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 80 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_80.D (m := 5) from colCert_73_73_80.bind2]
  exact alnAll_73_73_80 j hj hq

theorem leaf_73_73_85 (hp : 85 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 85 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 85 (transLenTr ⟨73, by decide⟩ 85 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 85 (transLenTr ⟨73, by decide⟩ 85 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 85 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 85 (transLenTr ⟨73, by decide⟩ 85 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_85.D (m := 5) from colCert_73_73_85.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 85 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_85.D (m := 5) from colCert_73_73_85.bind2]
  exact alnAll_73_73_85 j hj hq

theorem leaf_73_73_90 (hp : 90 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 90 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 90 (transLenTr ⟨73, by decide⟩ 90 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 90 (transLenTr ⟨73, by decide⟩ 90 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 90 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 90 (transLenTr ⟨73, by decide⟩ 90 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_90.D (m := 5) from colCert_73_73_90.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 90 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_90.D (m := 5) from colCert_73_73_90.bind2]
  exact alnAll_73_73_90 j hj hq

theorem leaf_73_73_95 (hp : 95 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 95 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 95 (transLenTr ⟨73, by decide⟩ 95 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 95 (transLenTr ⟨73, by decide⟩ 95 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 95 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 95 (transLenTr ⟨73, by decide⟩ 95 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_95.D (m := 5) from colCert_73_73_95.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 95 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_95.D (m := 5) from colCert_73_73_95.bind2]
  exact alnAll_73_73_95 j hj hq

theorem leaf_73_73_100 (hp : 100 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 100 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 100 (transLenTr ⟨73, by decide⟩ 100 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 100 (transLenTr ⟨73, by decide⟩ 100 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 100 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 100 (transLenTr ⟨73, by decide⟩ 100 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_100.D (m := 5) from colCert_73_73_100.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 100 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_100.D (m := 5) from colCert_73_73_100.bind2]
  exact alnAll_73_73_100 j hj hq

theorem leaf_73_73_105 (hp : 105 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 105 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 105 (transLenTr ⟨73, by decide⟩ 105 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 105 (transLenTr ⟨73, by decide⟩ 105 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 105 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 105 (transLenTr ⟨73, by decide⟩ 105 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_105.D (m := 5) from colCert_73_73_105.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 105 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_105.D (m := 5) from colCert_73_73_105.bind2]
  exact alnAll_73_73_105 j hj hq

theorem leaf_73_73_110 (hp : 110 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 110 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 110 (transLenTr ⟨73, by decide⟩ 110 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 110 (transLenTr ⟨73, by decide⟩ 110 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 110 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 110 (transLenTr ⟨73, by decide⟩ 110 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_110.D (m := 5) from colCert_73_73_110.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 110 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_110.D (m := 5) from colCert_73_73_110.bind2]
  exact alnAll_73_73_110 j hj hq

theorem leaf_73_73_115 (hp : 115 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 115 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 115 (transLenTr ⟨73, by decide⟩ 115 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 115 (transLenTr ⟨73, by decide⟩ 115 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 115 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 115 (transLenTr ⟨73, by decide⟩ 115 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_115.D (m := 5) from colCert_73_73_115.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 115 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_115.D (m := 5) from colCert_73_73_115.bind2]
  exact alnAll_73_73_115 j hj hq

theorem leaf_73_73_120 (hp : 120 < (Q2.transData.getD 73 []).length)
    (j : Nat) (hj : j < (repChars.getD 73 []).length)
    (hq : (normIsRep.getD 73 []).getD j false = true) :
    species (Q2.reps (⟨73, by decide⟩ : Fin 148)) (colE2 ⟨73, by decide⟩ 120 hp)
        (rowE2 (⟨73, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨73, by decide⟩ : Fin 148))
        (colE1 ⟨73, by decide⟩ 120 (transLenTr ⟨73, by decide⟩ 120 hp))
        (rowE1 (⟨73, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨73, by decide⟩ : Fin 148) ⟨73, by decide⟩ _
      (validAt ⟨73, by decide⟩ (listedAt ⟨73, by decide⟩ hj))
      (colE1 ⟨73, by decide⟩ 120 (transLenTr ⟨73, by decide⟩ 120 hp)) T73_73
      hfix73_73 hinj73_73 hcardT73_73
      (fun i => conj_mem_of_fixedPoints _ _ (T73_73 i) (hfix73_73 i) _)
      ⟨73, by decide⟩ ⟨73, by decide⟩ _
      (Q2.validAt ⟨73, by decide⟩ (Q2.listedAt ⟨73, by decide⟩
        (alnCheck_rep ⟨73, by decide⟩ hj hq).1))
      (colE2 ⟨73, by decide⟩ 120 hp) Q2.T73_73_2 Q2.hfix73_73_2 Q2.hinj73_73_2
      Q2.hcardT73_73_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T73_73_2 i) (Q2.hfix73_73_2 i) _)
      ?_).symm
  rw [show colData1 (⟨73, by decide⟩ : Fin 148)
        ((colE1 ⟨73, by decide⟩ 120 (transLenTr ⟨73, by decide⟩ 120 hp) : ↥(reps ⟨73, by decide⟩)) : Coordinate 1)
        T73_73 = colFn colCert_73_73_120.D (m := 5) from colCert_73_73_120.bind1,
    show colData2 (⟨73, by decide⟩ : Fin 148)
        ((colE2 ⟨73, by decide⟩ 120 hp : ↥(Q2.reps ⟨73, by decide⟩)) : Coordinate 2)
        Q2.T73_73_2 = colFn colCert_73_73_120.D (m := 5) from colCert_73_73_120.bind2]
  exact alnAll_73_73_120 j hj hq

theorem leaf_74_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T74_8
      hfix74_8 hinj74_8 hcardT74_8
      (fun i => conj_mem_of_fixedPoints _ _ (T74_8 i) (hfix74_8 i) _)
      ⟨74, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T74_8_2 Q2.hfix74_8_2 Q2.hinj74_8_2
      Q2.hcardT74_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_8_2 i) (Q2.hfix74_8_2 i) _)
      colCert_74_8_0.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T74_8
      hfix74_8 hinj74_8 hcardT74_8
      (fun i => conj_mem_of_fixedPoints _ _ (T74_8 i) (hfix74_8 i) _)
      ⟨74, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T74_8_2 Q2.hfix74_8_2 Q2.hinj74_8_2
      Q2.hcardT74_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_8_2 i) (Q2.hfix74_8_2 i) _)
      colCert_74_8_1.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T74_8
      hfix74_8 hinj74_8 hcardT74_8
      (fun i => conj_mem_of_fixedPoints _ _ (T74_8 i) (hfix74_8 i) _)
      ⟨74, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T74_8_2 Q2.hfix74_8_2 Q2.hinj74_8_2
      Q2.hcardT74_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_8_2 i) (Q2.hfix74_8_2 i) _)
      colCert_74_8_2.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T74_8
      hfix74_8 hinj74_8 hcardT74_8
      (fun i => conj_mem_of_fixedPoints _ _ (T74_8 i) (hfix74_8 i) _)
      ⟨74, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T74_8_2 Q2.hfix74_8_2 Q2.hinj74_8_2
      Q2.hcardT74_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_8_2 i) (Q2.hfix74_8_2 i) _)
      colCert_74_8_3.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T74_8
      hfix74_8 hinj74_8 hcardT74_8
      (fun i => conj_mem_of_fixedPoints _ _ (T74_8 i) (hfix74_8 i) _)
      ⟨74, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T74_8_2 Q2.hfix74_8_2 Q2.hinj74_8_2
      Q2.hcardT74_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_8_2 i) (Q2.hfix74_8_2 i) _)
      colCert_74_8_4.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T74_12
      hfix74_12 hinj74_12 hcardT74_12
      (fun i => conj_mem_of_fixedPoints _ _ (T74_12 i) (hfix74_12 i) _)
      ⟨74, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T74_12_2 Q2.hfix74_12_2 Q2.hinj74_12_2
      Q2.hcardT74_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_12_2 i) (Q2.hfix74_12_2 i) _)
      colCert_74_12_0.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T74_12
      hfix74_12 hinj74_12 hcardT74_12
      (fun i => conj_mem_of_fixedPoints _ _ (T74_12 i) (hfix74_12 i) _)
      ⟨74, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T74_12_2 Q2.hfix74_12_2 Q2.hinj74_12_2
      Q2.hcardT74_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_12_2 i) (Q2.hfix74_12_2 i) _)
      colCert_74_12_1.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T74_12
      hfix74_12 hinj74_12 hcardT74_12
      (fun i => conj_mem_of_fixedPoints _ _ (T74_12 i) (hfix74_12 i) _)
      ⟨74, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T74_12_2 Q2.hfix74_12_2 Q2.hinj74_12_2
      Q2.hcardT74_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_12_2 i) (Q2.hfix74_12_2 i) _)
      colCert_74_12_2.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T74_12
      hfix74_12 hinj74_12 hcardT74_12
      (fun i => conj_mem_of_fixedPoints _ _ (T74_12 i) (hfix74_12 i) _)
      ⟨74, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T74_12_2 Q2.hfix74_12_2 Q2.hinj74_12_2
      Q2.hcardT74_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_12_2 i) (Q2.hfix74_12_2 i) _)
      colCert_74_12_3.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T74_12
      hfix74_12 hinj74_12 hcardT74_12
      (fun i => conj_mem_of_fixedPoints _ _ (T74_12 i) (hfix74_12 i) _)
      ⟨74, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T74_12_2 Q2.hfix74_12_2 Q2.hinj74_12_2
      Q2.hcardT74_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_12_2 i) (Q2.hfix74_12_2 i) _)
      colCert_74_12_4.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T74_26
      hfix74_26 hinj74_26 hcardT74_26
      (fun i => conj_mem_of_fixedPoints _ _ (T74_26 i) (hfix74_26 i) _)
      ⟨74, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T74_26_2 Q2.hfix74_26_2 Q2.hinj74_26_2
      Q2.hcardT74_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_26_2 i) (Q2.hfix74_26_2 i) _)
      colCert_74_26_0.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T74_26
      hfix74_26 hinj74_26 hcardT74_26
      (fun i => conj_mem_of_fixedPoints _ _ (T74_26 i) (hfix74_26 i) _)
      ⟨74, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T74_26_2 Q2.hfix74_26_2 Q2.hinj74_26_2
      Q2.hcardT74_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_26_2 i) (Q2.hfix74_26_2 i) _)
      colCert_74_26_1.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T74_26
      hfix74_26 hinj74_26 hcardT74_26
      (fun i => conj_mem_of_fixedPoints _ _ (T74_26 i) (hfix74_26 i) _)
      ⟨74, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T74_26_2 Q2.hfix74_26_2 Q2.hinj74_26_2
      Q2.hcardT74_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_26_2 i) (Q2.hfix74_26_2 i) _)
      colCert_74_26_2.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T74_26
      hfix74_26 hinj74_26 hcardT74_26
      (fun i => conj_mem_of_fixedPoints _ _ (T74_26 i) (hfix74_26 i) _)
      ⟨74, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T74_26_2 Q2.hfix74_26_2 Q2.hinj74_26_2
      Q2.hcardT74_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_26_2 i) (Q2.hfix74_26_2 i) _)
      colCert_74_26_3.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T74_26
      hfix74_26 hinj74_26 hcardT74_26
      (fun i => conj_mem_of_fixedPoints _ _ (T74_26 i) (hfix74_26 i) _)
      ⟨74, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T74_26_2 Q2.hfix74_26_2 Q2.hinj74_26_2
      Q2.hcardT74_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_26_2 i) (Q2.hfix74_26_2 i) _)
      colCert_74_26_4.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T74_26
      hfix74_26 hinj74_26 hcardT74_26
      (fun i => conj_mem_of_fixedPoints _ _ (T74_26 i) (hfix74_26 i) _)
      ⟨74, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T74_26_2 Q2.hfix74_26_2 Q2.hinj74_26_2
      Q2.hcardT74_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_26_2 i) (Q2.hfix74_26_2 i) _)
      colCert_74_26_5.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T74_26
      hfix74_26 hinj74_26 hcardT74_26
      (fun i => conj_mem_of_fixedPoints _ _ (T74_26 i) (hfix74_26 i) _)
      ⟨74, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T74_26_2 Q2.hfix74_26_2 Q2.hinj74_26_2
      Q2.hcardT74_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_26_2 i) (Q2.hfix74_26_2 i) _)
      colCert_74_26_10.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T74_26
      hfix74_26 hinj74_26 hcardT74_26
      (fun i => conj_mem_of_fixedPoints _ _ (T74_26 i) (hfix74_26 i) _)
      ⟨74, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T74_26_2 Q2.hfix74_26_2 Q2.hinj74_26_2
      Q2.hcardT74_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_26_2 i) (Q2.hfix74_26_2 i) _)
      colCert_74_26_15.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T74_26
      hfix74_26 hinj74_26 hcardT74_26
      (fun i => conj_mem_of_fixedPoints _ _ (T74_26 i) (hfix74_26 i) _)
      ⟨74, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T74_26_2 Q2.hfix74_26_2 Q2.hinj74_26_2
      Q2.hcardT74_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_26_2 i) (Q2.hfix74_26_2 i) _)
      colCert_74_26_20.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T74_31
      hfix74_31 hinj74_31 hcardT74_31
      (fun i => conj_mem_of_fixedPoints _ _ (T74_31 i) (hfix74_31 i) _)
      ⟨74, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T74_31_2 Q2.hfix74_31_2 Q2.hinj74_31_2
      Q2.hcardT74_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_31_2 i) (Q2.hfix74_31_2 i) _)
      colCert_74_31_0.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T74_31
      hfix74_31 hinj74_31 hcardT74_31
      (fun i => conj_mem_of_fixedPoints _ _ (T74_31 i) (hfix74_31 i) _)
      ⟨74, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T74_31_2 Q2.hfix74_31_2 Q2.hinj74_31_2
      Q2.hcardT74_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_31_2 i) (Q2.hfix74_31_2 i) _)
      colCert_74_31_1.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T74_31
      hfix74_31 hinj74_31 hcardT74_31
      (fun i => conj_mem_of_fixedPoints _ _ (T74_31 i) (hfix74_31 i) _)
      ⟨74, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T74_31_2 Q2.hfix74_31_2 Q2.hinj74_31_2
      Q2.hcardT74_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_31_2 i) (Q2.hfix74_31_2 i) _)
      colCert_74_31_2.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T74_31
      hfix74_31 hinj74_31 hcardT74_31
      (fun i => conj_mem_of_fixedPoints _ _ (T74_31 i) (hfix74_31 i) _)
      ⟨74, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T74_31_2 Q2.hfix74_31_2 Q2.hinj74_31_2
      Q2.hcardT74_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_31_2 i) (Q2.hfix74_31_2 i) _)
      colCert_74_31_3.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T74_31
      hfix74_31 hinj74_31 hcardT74_31
      (fun i => conj_mem_of_fixedPoints _ _ (T74_31 i) (hfix74_31 i) _)
      ⟨74, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T74_31_2 Q2.hfix74_31_2 Q2.hinj74_31_2
      Q2.hcardT74_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_31_2 i) (Q2.hfix74_31_2 i) _)
      colCert_74_31_4.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T74_31
      hfix74_31 hinj74_31 hcardT74_31
      (fun i => conj_mem_of_fixedPoints _ _ (T74_31 i) (hfix74_31 i) _)
      ⟨74, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T74_31_2 Q2.hfix74_31_2 Q2.hinj74_31_2
      Q2.hcardT74_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_31_2 i) (Q2.hfix74_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T74_31 = colFn colCertDiv_74_31_5.D1 (m := 5) from colCertDiv_74_31_5.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 5 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T74_31_2 = colFn colCertDiv_74_31_5.D2 (m := 5) from colCertDiv_74_31_5.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_31_5_match


theorem leaf_74_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T74_31
      hfix74_31 hinj74_31 hcardT74_31
      (fun i => conj_mem_of_fixedPoints _ _ (T74_31 i) (hfix74_31 i) _)
      ⟨74, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T74_31_2 Q2.hfix74_31_2 Q2.hinj74_31_2
      Q2.hcardT74_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_31_2 i) (Q2.hfix74_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T74_31 = colFn colCertDiv_74_31_10.D1 (m := 5) from colCertDiv_74_31_10.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 10 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T74_31_2 = colFn colCertDiv_74_31_10.D2 (m := 5) from colCertDiv_74_31_10.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_31_10_match


theorem leaf_74_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T74_31
      hfix74_31 hinj74_31 hcardT74_31
      (fun i => conj_mem_of_fixedPoints _ _ (T74_31 i) (hfix74_31 i) _)
      ⟨74, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T74_31_2 Q2.hfix74_31_2 Q2.hinj74_31_2
      Q2.hcardT74_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_31_2 i) (Q2.hfix74_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T74_31 = colFn colCertDiv_74_31_15.D1 (m := 5) from colCertDiv_74_31_15.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T74_31_2 = colFn colCertDiv_74_31_15.D2 (m := 5) from colCertDiv_74_31_15.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_31_15_match


theorem leaf_74_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T74_31
      hfix74_31 hinj74_31 hcardT74_31
      (fun i => conj_mem_of_fixedPoints _ _ (T74_31 i) (hfix74_31 i) _)
      ⟨74, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T74_31_2 Q2.hfix74_31_2 Q2.hinj74_31_2
      Q2.hcardT74_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_31_2 i) (Q2.hfix74_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T74_31 = colFn colCertDiv_74_31_20.D1 (m := 5) from colCertDiv_74_31_20.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 20 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T74_31_2 = colFn colCertDiv_74_31_20.D2 (m := 5) from colCertDiv_74_31_20.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_31_20_match


theorem leaf_74_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T74_36
      hfix74_36 hinj74_36 hcardT74_36
      (fun i => conj_mem_of_fixedPoints _ _ (T74_36 i) (hfix74_36 i) _)
      ⟨74, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T74_36_2 Q2.hfix74_36_2 Q2.hinj74_36_2
      Q2.hcardT74_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_36_2 i) (Q2.hfix74_36_2 i) _)
      colCert_74_36_0.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T74_36
      hfix74_36 hinj74_36 hcardT74_36
      (fun i => conj_mem_of_fixedPoints _ _ (T74_36 i) (hfix74_36 i) _)
      ⟨74, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T74_36_2 Q2.hfix74_36_2 Q2.hinj74_36_2
      Q2.hcardT74_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_36_2 i) (Q2.hfix74_36_2 i) _)
      colCert_74_36_1.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T74_36
      hfix74_36 hinj74_36 hcardT74_36
      (fun i => conj_mem_of_fixedPoints _ _ (T74_36 i) (hfix74_36 i) _)
      ⟨74, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T74_36_2 Q2.hfix74_36_2 Q2.hinj74_36_2
      Q2.hcardT74_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_36_2 i) (Q2.hfix74_36_2 i) _)
      colCert_74_36_2.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T74_36
      hfix74_36 hinj74_36 hcardT74_36
      (fun i => conj_mem_of_fixedPoints _ _ (T74_36 i) (hfix74_36 i) _)
      ⟨74, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T74_36_2 Q2.hfix74_36_2 Q2.hinj74_36_2
      Q2.hcardT74_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_36_2 i) (Q2.hfix74_36_2 i) _)
      colCert_74_36_3.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T74_36
      hfix74_36 hinj74_36 hcardT74_36
      (fun i => conj_mem_of_fixedPoints _ _ (T74_36 i) (hfix74_36 i) _)
      ⟨74, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T74_36_2 Q2.hfix74_36_2 Q2.hinj74_36_2
      Q2.hcardT74_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_36_2 i) (Q2.hfix74_36_2 i) _)
      colCert_74_36_4.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T74_36
      hfix74_36 hinj74_36 hcardT74_36
      (fun i => conj_mem_of_fixedPoints _ _ (T74_36 i) (hfix74_36 i) _)
      ⟨74, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T74_36_2 Q2.hfix74_36_2 Q2.hinj74_36_2
      Q2.hcardT74_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_36_2 i) (Q2.hfix74_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T74_36 = colFn colCertDiv_74_36_5.D1 (m := 5) from colCertDiv_74_36_5.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T74_36_2 = colFn colCertDiv_74_36_5.D2 (m := 5) from colCertDiv_74_36_5.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_36_5_match


theorem leaf_74_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T74_36
      hfix74_36 hinj74_36 hcardT74_36
      (fun i => conj_mem_of_fixedPoints _ _ (T74_36 i) (hfix74_36 i) _)
      ⟨74, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T74_36_2 Q2.hfix74_36_2 Q2.hinj74_36_2
      Q2.hcardT74_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_36_2 i) (Q2.hfix74_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T74_36 = colFn colCertDiv_74_36_10.D1 (m := 5) from colCertDiv_74_36_10.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T74_36_2 = colFn colCertDiv_74_36_10.D2 (m := 5) from colCertDiv_74_36_10.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_36_10_match


theorem leaf_74_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T74_36
      hfix74_36 hinj74_36 hcardT74_36
      (fun i => conj_mem_of_fixedPoints _ _ (T74_36 i) (hfix74_36 i) _)
      ⟨74, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T74_36_2 Q2.hfix74_36_2 Q2.hinj74_36_2
      Q2.hcardT74_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_36_2 i) (Q2.hfix74_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T74_36 = colFn colCertDiv_74_36_15.D1 (m := 5) from colCertDiv_74_36_15.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 15 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T74_36_2 = colFn colCertDiv_74_36_15.D2 (m := 5) from colCertDiv_74_36_15.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_36_15_match


theorem leaf_74_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T74_36
      hfix74_36 hinj74_36 hcardT74_36
      (fun i => conj_mem_of_fixedPoints _ _ (T74_36 i) (hfix74_36 i) _)
      ⟨74, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T74_36_2 Q2.hfix74_36_2 Q2.hinj74_36_2
      Q2.hcardT74_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_36_2 i) (Q2.hfix74_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T74_36 = colFn colCertDiv_74_36_20.D1 (m := 5) from colCertDiv_74_36_20.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T74_36_2 = colFn colCertDiv_74_36_20.D2 (m := 5) from colCertDiv_74_36_20.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_36_20_match


theorem leaf_74_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T74_41
      hfix74_41 hinj74_41 hcardT74_41
      (fun i => conj_mem_of_fixedPoints _ _ (T74_41 i) (hfix74_41 i) _)
      ⟨74, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T74_41_2 Q2.hfix74_41_2 Q2.hinj74_41_2
      Q2.hcardT74_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_41_2 i) (Q2.hfix74_41_2 i) _)
      colCert_74_41_0.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T74_41
      hfix74_41 hinj74_41 hcardT74_41
      (fun i => conj_mem_of_fixedPoints _ _ (T74_41 i) (hfix74_41 i) _)
      ⟨74, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T74_41_2 Q2.hfix74_41_2 Q2.hinj74_41_2
      Q2.hcardT74_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_41_2 i) (Q2.hfix74_41_2 i) _)
      colCert_74_41_1.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T74_41
      hfix74_41 hinj74_41 hcardT74_41
      (fun i => conj_mem_of_fixedPoints _ _ (T74_41 i) (hfix74_41 i) _)
      ⟨74, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T74_41_2 Q2.hfix74_41_2 Q2.hinj74_41_2
      Q2.hcardT74_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_41_2 i) (Q2.hfix74_41_2 i) _)
      colCert_74_41_2.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T74_41
      hfix74_41 hinj74_41 hcardT74_41
      (fun i => conj_mem_of_fixedPoints _ _ (T74_41 i) (hfix74_41 i) _)
      ⟨74, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T74_41_2 Q2.hfix74_41_2 Q2.hinj74_41_2
      Q2.hcardT74_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_41_2 i) (Q2.hfix74_41_2 i) _)
      colCert_74_41_3.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T74_41
      hfix74_41 hinj74_41 hcardT74_41
      (fun i => conj_mem_of_fixedPoints _ _ (T74_41 i) (hfix74_41 i) _)
      ⟨74, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T74_41_2 Q2.hfix74_41_2 Q2.hinj74_41_2
      Q2.hcardT74_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_41_2 i) (Q2.hfix74_41_2 i) _)
      colCert_74_41_4.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T74_41
      hfix74_41 hinj74_41 hcardT74_41
      (fun i => conj_mem_of_fixedPoints _ _ (T74_41 i) (hfix74_41 i) _)
      ⟨74, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T74_41_2 Q2.hfix74_41_2 Q2.hinj74_41_2
      Q2.hcardT74_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_41_2 i) (Q2.hfix74_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T74_41 = colFn colCertDiv_74_41_5.D1 (m := 5) from colCertDiv_74_41_5.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T74_41_2 = colFn colCertDiv_74_41_5.D2 (m := 5) from colCertDiv_74_41_5.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_41_5_match


theorem leaf_74_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T74_41
      hfix74_41 hinj74_41 hcardT74_41
      (fun i => conj_mem_of_fixedPoints _ _ (T74_41 i) (hfix74_41 i) _)
      ⟨74, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T74_41_2 Q2.hfix74_41_2 Q2.hinj74_41_2
      Q2.hcardT74_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_41_2 i) (Q2.hfix74_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T74_41 = colFn colCertDiv_74_41_10.D1 (m := 5) from colCertDiv_74_41_10.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T74_41_2 = colFn colCertDiv_74_41_10.D2 (m := 5) from colCertDiv_74_41_10.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_41_10_match


theorem leaf_74_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T74_41
      hfix74_41 hinj74_41 hcardT74_41
      (fun i => conj_mem_of_fixedPoints _ _ (T74_41 i) (hfix74_41 i) _)
      ⟨74, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T74_41_2 Q2.hfix74_41_2 Q2.hinj74_41_2
      Q2.hcardT74_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_41_2 i) (Q2.hfix74_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T74_41 = colFn colCertDiv_74_41_15.D1 (m := 5) from colCertDiv_74_41_15.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 15 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T74_41_2 = colFn colCertDiv_74_41_15.D2 (m := 5) from colCertDiv_74_41_15.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_41_15_match


theorem leaf_74_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨74, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T74_41
      hfix74_41 hinj74_41 hcardT74_41
      (fun i => conj_mem_of_fixedPoints _ _ (T74_41 i) (hfix74_41 i) _)
      ⟨74, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T74_41_2 Q2.hfix74_41_2 Q2.hinj74_41_2
      Q2.hcardT74_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_41_2 i) (Q2.hfix74_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨74, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T74_41 = colFn colCertDiv_74_41_20.D1 (m := 5) from colCertDiv_74_41_20.bind1,
    show colData2 (⟨74, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T74_41_2 = colFn colCertDiv_74_41_20.D2 (m := 5) from colCertDiv_74_41_20.bind2]
  rw [alnId_74 j hj]
  exact fastcode_of_div ⟨74, by decide⟩ _ _ _
    ((alnId_74 j hj) ▸ Q2.listedAt (⟨74, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨74, by decide⟩ : Fin 148) hj hq).1) colCertDiv_74_41_20_match


theorem leaf_74_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T74_46
      hfix74_46 hinj74_46 hcardT74_46
      (fun i => conj_mem_of_fixedPoints _ _ (T74_46 i) (hfix74_46 i) _)
      ⟨74, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T74_46_2 Q2.hfix74_46_2 Q2.hinj74_46_2
      Q2.hcardT74_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_46_2 i) (Q2.hfix74_46_2 i) _)
      colCert_74_46_0.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T74_46
      hfix74_46 hinj74_46 hcardT74_46
      (fun i => conj_mem_of_fixedPoints _ _ (T74_46 i) (hfix74_46 i) _)
      ⟨74, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T74_46_2 Q2.hfix74_46_2 Q2.hinj74_46_2
      Q2.hcardT74_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_46_2 i) (Q2.hfix74_46_2 i) _)
      colCert_74_46_1.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T74_46
      hfix74_46 hinj74_46 hcardT74_46
      (fun i => conj_mem_of_fixedPoints _ _ (T74_46 i) (hfix74_46 i) _)
      ⟨74, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T74_46_2 Q2.hfix74_46_2 Q2.hinj74_46_2
      Q2.hcardT74_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_46_2 i) (Q2.hfix74_46_2 i) _)
      colCert_74_46_2.hD ?_).symm
  rw [alnId_74 j hj]


theorem leaf_74_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 74 []).length)
    (hq : (normIsRep.getD 74 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨74, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨74, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨74, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨74, by decide⟩ (listedAt ⟨74, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T74_46
      hfix74_46 hinj74_46 hcardT74_46
      (fun i => conj_mem_of_fixedPoints _ _ (T74_46 i) (hfix74_46 i) _)
      ⟨74, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨74, by decide⟩ (Q2.listedAt ⟨74, by decide⟩
        (alnCheck_rep ⟨74, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T74_46_2 Q2.hfix74_46_2 Q2.hinj74_46_2
      Q2.hcardT74_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T74_46_2 i) (Q2.hfix74_46_2 i) _)
      colCert_74_46_3.hD ?_).symm
  rw [alnId_74 j hj]


end LeanDring.P5Presentation
