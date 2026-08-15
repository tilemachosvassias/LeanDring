/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C038
import LeanDring.P5.Data.ColRestCheap.C147
import LeanDring.P5.Data.ColRestCheap.C148
import LeanDring.P5.Data.ColRestCheap.C149
import LeanDring.P5.Data.ColRestCheap.C150
import LeanDring.P5.Data.ColRestCheap.C151
import LeanDring.P5.Data.EntryK.C015
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C045
import LeanDring.P5.Data.SpeciesDiv.C046

/-! # Stage-5 leaves, chunk 6 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_61_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T61_19
      hfix61_19 hinj61_19 hcardT61_19
      (fun i => conj_mem_of_fixedPoints _ _ (T61_19 i) (hfix61_19 i) _)
      ⟨61, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T61_19_2 Q2.hfix61_19_2 Q2.hinj61_19_2
      Q2.hcardT61_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_19_2 i) (Q2.hfix61_19_2 i) _)
      colCert_61_19_15.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T61_19
      hfix61_19 hinj61_19 hcardT61_19
      (fun i => conj_mem_of_fixedPoints _ _ (T61_19 i) (hfix61_19 i) _)
      ⟨61, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T61_19_2 Q2.hfix61_19_2 Q2.hinj61_19_2
      Q2.hcardT61_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_19_2 i) (Q2.hfix61_19_2 i) _)
      colCert_61_19_20.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T61_29
      hfix61_29 hinj61_29 hcardT61_29
      (fun i => conj_mem_of_fixedPoints _ _ (T61_29 i) (hfix61_29 i) _)
      ⟨61, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T61_29_2 Q2.hfix61_29_2 Q2.hinj61_29_2
      Q2.hcardT61_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_29_2 i) (Q2.hfix61_29_2 i) _)
      colCert_61_29_0.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T61_29
      hfix61_29 hinj61_29 hcardT61_29
      (fun i => conj_mem_of_fixedPoints _ _ (T61_29 i) (hfix61_29 i) _)
      ⟨61, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T61_29_2 Q2.hfix61_29_2 Q2.hinj61_29_2
      Q2.hcardT61_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_29_2 i) (Q2.hfix61_29_2 i) _)
      colCert_61_29_1.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T61_29
      hfix61_29 hinj61_29 hcardT61_29
      (fun i => conj_mem_of_fixedPoints _ _ (T61_29 i) (hfix61_29 i) _)
      ⟨61, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T61_29_2 Q2.hfix61_29_2 Q2.hinj61_29_2
      Q2.hcardT61_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_29_2 i) (Q2.hfix61_29_2 i) _)
      colCert_61_29_2.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T61_29
      hfix61_29 hinj61_29 hcardT61_29
      (fun i => conj_mem_of_fixedPoints _ _ (T61_29 i) (hfix61_29 i) _)
      ⟨61, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T61_29_2 Q2.hfix61_29_2 Q2.hinj61_29_2
      Q2.hcardT61_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_29_2 i) (Q2.hfix61_29_2 i) _)
      colCert_61_29_3.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T61_29
      hfix61_29 hinj61_29 hcardT61_29
      (fun i => conj_mem_of_fixedPoints _ _ (T61_29 i) (hfix61_29 i) _)
      ⟨61, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T61_29_2 Q2.hfix61_29_2 Q2.hinj61_29_2
      Q2.hcardT61_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_29_2 i) (Q2.hfix61_29_2 i) _)
      colCert_61_29_4.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T61_29
      hfix61_29 hinj61_29 hcardT61_29
      (fun i => conj_mem_of_fixedPoints _ _ (T61_29 i) (hfix61_29 i) _)
      ⟨61, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T61_29_2 Q2.hfix61_29_2 Q2.hinj61_29_2
      Q2.hcardT61_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_29_2 i) (Q2.hfix61_29_2 i) _)
      colCert_61_29_5.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T61_29
      hfix61_29 hinj61_29 hcardT61_29
      (fun i => conj_mem_of_fixedPoints _ _ (T61_29 i) (hfix61_29 i) _)
      ⟨61, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T61_29_2 Q2.hfix61_29_2 Q2.hinj61_29_2
      Q2.hcardT61_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_29_2 i) (Q2.hfix61_29_2 i) _)
      colCert_61_29_10.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T61_29
      hfix61_29 hinj61_29 hcardT61_29
      (fun i => conj_mem_of_fixedPoints _ _ (T61_29 i) (hfix61_29 i) _)
      ⟨61, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T61_29_2 Q2.hfix61_29_2 Q2.hinj61_29_2
      Q2.hcardT61_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_29_2 i) (Q2.hfix61_29_2 i) _)
      colCert_61_29_15.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T61_29
      hfix61_29 hinj61_29 hcardT61_29
      (fun i => conj_mem_of_fixedPoints _ _ (T61_29 i) (hfix61_29 i) _)
      ⟨61, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T61_29_2 Q2.hfix61_29_2 Q2.hinj61_29_2
      Q2.hcardT61_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_29_2 i) (Q2.hfix61_29_2 i) _)
      colCert_61_29_20.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T61_34
      hfix61_34 hinj61_34 hcardT61_34
      (fun i => conj_mem_of_fixedPoints _ _ (T61_34 i) (hfix61_34 i) _)
      ⟨61, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T61_34_2 Q2.hfix61_34_2 Q2.hinj61_34_2
      Q2.hcardT61_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_34_2 i) (Q2.hfix61_34_2 i) _)
      colCert_61_34_0.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T61_34
      hfix61_34 hinj61_34 hcardT61_34
      (fun i => conj_mem_of_fixedPoints _ _ (T61_34 i) (hfix61_34 i) _)
      ⟨61, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T61_34_2 Q2.hfix61_34_2 Q2.hinj61_34_2
      Q2.hcardT61_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_34_2 i) (Q2.hfix61_34_2 i) _)
      colCert_61_34_1.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T61_34
      hfix61_34 hinj61_34 hcardT61_34
      (fun i => conj_mem_of_fixedPoints _ _ (T61_34 i) (hfix61_34 i) _)
      ⟨61, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T61_34_2 Q2.hfix61_34_2 Q2.hinj61_34_2
      Q2.hcardT61_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_34_2 i) (Q2.hfix61_34_2 i) _)
      colCert_61_34_2.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T61_34
      hfix61_34 hinj61_34 hcardT61_34
      (fun i => conj_mem_of_fixedPoints _ _ (T61_34 i) (hfix61_34 i) _)
      ⟨61, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T61_34_2 Q2.hfix61_34_2 Q2.hinj61_34_2
      Q2.hcardT61_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_34_2 i) (Q2.hfix61_34_2 i) _)
      colCert_61_34_3.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T61_34
      hfix61_34 hinj61_34 hcardT61_34
      (fun i => conj_mem_of_fixedPoints _ _ (T61_34 i) (hfix61_34 i) _)
      ⟨61, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T61_34_2 Q2.hfix61_34_2 Q2.hinj61_34_2
      Q2.hcardT61_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_34_2 i) (Q2.hfix61_34_2 i) _)
      colCert_61_34_4.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T61_34
      hfix61_34 hinj61_34 hcardT61_34
      (fun i => conj_mem_of_fixedPoints _ _ (T61_34 i) (hfix61_34 i) _)
      ⟨61, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T61_34_2 Q2.hfix61_34_2 Q2.hinj61_34_2
      Q2.hcardT61_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_34_2 i) (Q2.hfix61_34_2 i) _)
      colCert_61_34_5.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T61_34
      hfix61_34 hinj61_34 hcardT61_34
      (fun i => conj_mem_of_fixedPoints _ _ (T61_34 i) (hfix61_34 i) _)
      ⟨61, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T61_34_2 Q2.hfix61_34_2 Q2.hinj61_34_2
      Q2.hcardT61_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_34_2 i) (Q2.hfix61_34_2 i) _)
      colCert_61_34_10.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T61_34
      hfix61_34 hinj61_34 hcardT61_34
      (fun i => conj_mem_of_fixedPoints _ _ (T61_34 i) (hfix61_34 i) _)
      ⟨61, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T61_34_2 Q2.hfix61_34_2 Q2.hinj61_34_2
      Q2.hcardT61_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_34_2 i) (Q2.hfix61_34_2 i) _)
      colCert_61_34_15.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T61_34
      hfix61_34 hinj61_34 hcardT61_34
      (fun i => conj_mem_of_fixedPoints _ _ (T61_34 i) (hfix61_34 i) _)
      ⟨61, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T61_34_2 Q2.hfix61_34_2 Q2.hinj61_34_2
      Q2.hcardT61_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_34_2 i) (Q2.hfix61_34_2 i) _)
      colCert_61_34_20.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T61_39
      hfix61_39 hinj61_39 hcardT61_39
      (fun i => conj_mem_of_fixedPoints _ _ (T61_39 i) (hfix61_39 i) _)
      ⟨61, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T61_39_2 Q2.hfix61_39_2 Q2.hinj61_39_2
      Q2.hcardT61_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_39_2 i) (Q2.hfix61_39_2 i) _)
      colCert_61_39_0.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T61_39
      hfix61_39 hinj61_39 hcardT61_39
      (fun i => conj_mem_of_fixedPoints _ _ (T61_39 i) (hfix61_39 i) _)
      ⟨61, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T61_39_2 Q2.hfix61_39_2 Q2.hinj61_39_2
      Q2.hcardT61_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_39_2 i) (Q2.hfix61_39_2 i) _)
      colCert_61_39_1.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T61_39
      hfix61_39 hinj61_39 hcardT61_39
      (fun i => conj_mem_of_fixedPoints _ _ (T61_39 i) (hfix61_39 i) _)
      ⟨61, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T61_39_2 Q2.hfix61_39_2 Q2.hinj61_39_2
      Q2.hcardT61_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_39_2 i) (Q2.hfix61_39_2 i) _)
      colCert_61_39_2.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T61_39
      hfix61_39 hinj61_39 hcardT61_39
      (fun i => conj_mem_of_fixedPoints _ _ (T61_39 i) (hfix61_39 i) _)
      ⟨61, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T61_39_2 Q2.hfix61_39_2 Q2.hinj61_39_2
      Q2.hcardT61_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_39_2 i) (Q2.hfix61_39_2 i) _)
      colCert_61_39_3.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T61_39
      hfix61_39 hinj61_39 hcardT61_39
      (fun i => conj_mem_of_fixedPoints _ _ (T61_39 i) (hfix61_39 i) _)
      ⟨61, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T61_39_2 Q2.hfix61_39_2 Q2.hinj61_39_2
      Q2.hcardT61_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_39_2 i) (Q2.hfix61_39_2 i) _)
      colCert_61_39_4.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T61_39
      hfix61_39 hinj61_39 hcardT61_39
      (fun i => conj_mem_of_fixedPoints _ _ (T61_39 i) (hfix61_39 i) _)
      ⟨61, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T61_39_2 Q2.hfix61_39_2 Q2.hinj61_39_2
      Q2.hcardT61_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_39_2 i) (Q2.hfix61_39_2 i) _)
      colCert_61_39_5.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T61_39
      hfix61_39 hinj61_39 hcardT61_39
      (fun i => conj_mem_of_fixedPoints _ _ (T61_39 i) (hfix61_39 i) _)
      ⟨61, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T61_39_2 Q2.hfix61_39_2 Q2.hinj61_39_2
      Q2.hcardT61_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_39_2 i) (Q2.hfix61_39_2 i) _)
      colCert_61_39_10.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T61_39
      hfix61_39 hinj61_39 hcardT61_39
      (fun i => conj_mem_of_fixedPoints _ _ (T61_39 i) (hfix61_39 i) _)
      ⟨61, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T61_39_2 Q2.hfix61_39_2 Q2.hinj61_39_2
      Q2.hcardT61_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_39_2 i) (Q2.hfix61_39_2 i) _)
      colCert_61_39_15.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T61_39
      hfix61_39 hinj61_39 hcardT61_39
      (fun i => conj_mem_of_fixedPoints _ _ (T61_39 i) (hfix61_39 i) _)
      ⟨61, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T61_39_2 Q2.hfix61_39_2 Q2.hinj61_39_2
      Q2.hcardT61_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_39_2 i) (Q2.hfix61_39_2 i) _)
      colCert_61_39_20.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T61_44
      hfix61_44 hinj61_44 hcardT61_44
      (fun i => conj_mem_of_fixedPoints _ _ (T61_44 i) (hfix61_44 i) _)
      ⟨61, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T61_44_2 Q2.hfix61_44_2 Q2.hinj61_44_2
      Q2.hcardT61_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_44_2 i) (Q2.hfix61_44_2 i) _)
      colCert_61_44_0.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T61_44
      hfix61_44 hinj61_44 hcardT61_44
      (fun i => conj_mem_of_fixedPoints _ _ (T61_44 i) (hfix61_44 i) _)
      ⟨61, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T61_44_2 Q2.hfix61_44_2 Q2.hinj61_44_2
      Q2.hcardT61_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_44_2 i) (Q2.hfix61_44_2 i) _)
      colCert_61_44_1.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T61_44
      hfix61_44 hinj61_44 hcardT61_44
      (fun i => conj_mem_of_fixedPoints _ _ (T61_44 i) (hfix61_44 i) _)
      ⟨61, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T61_44_2 Q2.hfix61_44_2 Q2.hinj61_44_2
      Q2.hcardT61_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_44_2 i) (Q2.hfix61_44_2 i) _)
      colCert_61_44_2.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T61_44
      hfix61_44 hinj61_44 hcardT61_44
      (fun i => conj_mem_of_fixedPoints _ _ (T61_44 i) (hfix61_44 i) _)
      ⟨61, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T61_44_2 Q2.hfix61_44_2 Q2.hinj61_44_2
      Q2.hcardT61_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_44_2 i) (Q2.hfix61_44_2 i) _)
      colCert_61_44_3.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T61_44
      hfix61_44 hinj61_44 hcardT61_44
      (fun i => conj_mem_of_fixedPoints _ _ (T61_44 i) (hfix61_44 i) _)
      ⟨61, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T61_44_2 Q2.hfix61_44_2 Q2.hinj61_44_2
      Q2.hcardT61_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_44_2 i) (Q2.hfix61_44_2 i) _)
      colCert_61_44_4.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T61_44
      hfix61_44 hinj61_44 hcardT61_44
      (fun i => conj_mem_of_fixedPoints _ _ (T61_44 i) (hfix61_44 i) _)
      ⟨61, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T61_44_2 Q2.hfix61_44_2 Q2.hinj61_44_2
      Q2.hcardT61_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_44_2 i) (Q2.hfix61_44_2 i) _)
      colCert_61_44_5.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T61_44
      hfix61_44 hinj61_44 hcardT61_44
      (fun i => conj_mem_of_fixedPoints _ _ (T61_44 i) (hfix61_44 i) _)
      ⟨61, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T61_44_2 Q2.hfix61_44_2 Q2.hinj61_44_2
      Q2.hcardT61_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_44_2 i) (Q2.hfix61_44_2 i) _)
      colCert_61_44_10.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T61_44
      hfix61_44 hinj61_44 hcardT61_44
      (fun i => conj_mem_of_fixedPoints _ _ (T61_44 i) (hfix61_44 i) _)
      ⟨61, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T61_44_2 Q2.hfix61_44_2 Q2.hinj61_44_2
      Q2.hcardT61_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_44_2 i) (Q2.hfix61_44_2 i) _)
      colCert_61_44_15.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T61_44
      hfix61_44 hinj61_44 hcardT61_44
      (fun i => conj_mem_of_fixedPoints _ _ (T61_44 i) (hfix61_44 i) _)
      ⟨61, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T61_44_2 Q2.hfix61_44_2 Q2.hinj61_44_2
      Q2.hcardT61_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_44_2 i) (Q2.hfix61_44_2 i) _)
      colCert_61_44_20.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T61_49
      hfix61_49 hinj61_49 hcardT61_49
      (fun i => conj_mem_of_fixedPoints _ _ (T61_49 i) (hfix61_49 i) _)
      ⟨61, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T61_49_2 Q2.hfix61_49_2 Q2.hinj61_49_2
      Q2.hcardT61_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_49_2 i) (Q2.hfix61_49_2 i) _)
      colCert_61_49_0.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T61_49
      hfix61_49 hinj61_49 hcardT61_49
      (fun i => conj_mem_of_fixedPoints _ _ (T61_49 i) (hfix61_49 i) _)
      ⟨61, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T61_49_2 Q2.hfix61_49_2 Q2.hinj61_49_2
      Q2.hcardT61_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_49_2 i) (Q2.hfix61_49_2 i) _)
      colCert_61_49_1.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T61_49
      hfix61_49 hinj61_49 hcardT61_49
      (fun i => conj_mem_of_fixedPoints _ _ (T61_49 i) (hfix61_49 i) _)
      ⟨61, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T61_49_2 Q2.hfix61_49_2 Q2.hinj61_49_2
      Q2.hcardT61_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_49_2 i) (Q2.hfix61_49_2 i) _)
      colCert_61_49_2.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T61_49
      hfix61_49 hinj61_49 hcardT61_49
      (fun i => conj_mem_of_fixedPoints _ _ (T61_49 i) (hfix61_49 i) _)
      ⟨61, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T61_49_2 Q2.hfix61_49_2 Q2.hinj61_49_2
      Q2.hcardT61_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_49_2 i) (Q2.hfix61_49_2 i) _)
      colCert_61_49_3.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T61_49
      hfix61_49 hinj61_49 hcardT61_49
      (fun i => conj_mem_of_fixedPoints _ _ (T61_49 i) (hfix61_49 i) _)
      ⟨61, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T61_49_2 Q2.hfix61_49_2 Q2.hinj61_49_2
      Q2.hcardT61_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_49_2 i) (Q2.hfix61_49_2 i) _)
      colCert_61_49_4.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T61_49
      hfix61_49 hinj61_49 hcardT61_49
      (fun i => conj_mem_of_fixedPoints _ _ (T61_49 i) (hfix61_49 i) _)
      ⟨61, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T61_49_2 Q2.hfix61_49_2 Q2.hinj61_49_2
      Q2.hcardT61_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_49_2 i) (Q2.hfix61_49_2 i) _)
      colCert_61_49_5.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T61_49
      hfix61_49 hinj61_49 hcardT61_49
      (fun i => conj_mem_of_fixedPoints _ _ (T61_49 i) (hfix61_49 i) _)
      ⟨61, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T61_49_2 Q2.hfix61_49_2 Q2.hinj61_49_2
      Q2.hcardT61_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_49_2 i) (Q2.hfix61_49_2 i) _)
      colCert_61_49_10.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T61_49
      hfix61_49 hinj61_49 hcardT61_49
      (fun i => conj_mem_of_fixedPoints _ _ (T61_49 i) (hfix61_49 i) _)
      ⟨61, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T61_49_2 Q2.hfix61_49_2 Q2.hinj61_49_2
      Q2.hcardT61_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_49_2 i) (Q2.hfix61_49_2 i) _)
      colCert_61_49_15.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T61_49
      hfix61_49 hinj61_49 hcardT61_49
      (fun i => conj_mem_of_fixedPoints _ _ (T61_49 i) (hfix61_49 i) _)
      ⟨61, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T61_49_2 Q2.hfix61_49_2 Q2.hinj61_49_2
      Q2.hcardT61_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_49_2 i) (Q2.hfix61_49_2 i) _)
      colCert_61_49_20.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_0 (hp : 0 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 0 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 0 (transLenTr ⟨61, by decide⟩ 0 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 0 (transLenTr ⟨61, by decide⟩ 0 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 0 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_0.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_1 (hp : 1 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 1 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 1 (transLenTr ⟨61, by decide⟩ 1 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 1 (transLenTr ⟨61, by decide⟩ 1 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 1 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_1.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_2 (hp : 2 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 2 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 2 (transLenTr ⟨61, by decide⟩ 2 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 2 (transLenTr ⟨61, by decide⟩ 2 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 2 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_2.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_3 (hp : 3 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 3 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 3 (transLenTr ⟨61, by decide⟩ 3 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 3 (transLenTr ⟨61, by decide⟩ 3 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 3 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_3.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_4 (hp : 4 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 4 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 4 (transLenTr ⟨61, by decide⟩ 4 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 4 (transLenTr ⟨61, by decide⟩ 4 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 4 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_4.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_5 (hp : 5 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 5 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 5 (transLenTr ⟨61, by decide⟩ 5 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 5 (transLenTr ⟨61, by decide⟩ 5 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 5 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_5.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_6 (hp : 6 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 6 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 6 (transLenTr ⟨61, by decide⟩ 6 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 6 (transLenTr ⟨61, by decide⟩ 6 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 6 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_6.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_7 (hp : 7 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 7 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 7 (transLenTr ⟨61, by decide⟩ 7 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 7 (transLenTr ⟨61, by decide⟩ 7 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 7 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_7.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_8 (hp : 8 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 8 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 8 (transLenTr ⟨61, by decide⟩ 8 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 8 (transLenTr ⟨61, by decide⟩ 8 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 8 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_8.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_9 (hp : 9 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 9 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 9 (transLenTr ⟨61, by decide⟩ 9 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 9 (transLenTr ⟨61, by decide⟩ 9 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 9 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_9.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_10 (hp : 10 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 10 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 10 (transLenTr ⟨61, by decide⟩ 10 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 10 (transLenTr ⟨61, by decide⟩ 10 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 10 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_10.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_11 (hp : 11 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 11 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 11 (transLenTr ⟨61, by decide⟩ 11 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 11 (transLenTr ⟨61, by decide⟩ 11 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 11 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_11.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_12 (hp : 12 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 12 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 12 (transLenTr ⟨61, by decide⟩ 12 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 12 (transLenTr ⟨61, by decide⟩ 12 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 12 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_12.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_13 (hp : 13 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 13 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 13 (transLenTr ⟨61, by decide⟩ 13 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 13 (transLenTr ⟨61, by decide⟩ 13 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 13 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_13.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_14 (hp : 14 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 14 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 14 (transLenTr ⟨61, by decide⟩ 14 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 14 (transLenTr ⟨61, by decide⟩ 14 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 14 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_14.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_15 (hp : 15 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 15 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 15 (transLenTr ⟨61, by decide⟩ 15 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 15 (transLenTr ⟨61, by decide⟩ 15 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 15 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_15.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_16 (hp : 16 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 16 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 16 (transLenTr ⟨61, by decide⟩ 16 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 16 (transLenTr ⟨61, by decide⟩ 16 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 16 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_16.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_17 (hp : 17 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 17 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 17 (transLenTr ⟨61, by decide⟩ 17 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 17 (transLenTr ⟨61, by decide⟩ 17 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 17 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_17.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_18 (hp : 18 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 18 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 18 (transLenTr ⟨61, by decide⟩ 18 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 18 (transLenTr ⟨61, by decide⟩ 18 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 18 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_18.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_19 (hp : 19 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 19 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 19 (transLenTr ⟨61, by decide⟩ 19 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 19 (transLenTr ⟨61, by decide⟩ 19 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 19 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_19.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_20 (hp : 20 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 20 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 20 (transLenTr ⟨61, by decide⟩ 20 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 20 (transLenTr ⟨61, by decide⟩ 20 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 20 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_20.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_21 (hp : 21 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 21 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 21 (transLenTr ⟨61, by decide⟩ 21 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 21 (transLenTr ⟨61, by decide⟩ 21 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 21 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_21.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_22 (hp : 22 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 22 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 22 (transLenTr ⟨61, by decide⟩ 22 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 22 (transLenTr ⟨61, by decide⟩ 22 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 22 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_22.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_23 (hp : 23 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 23 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 23 (transLenTr ⟨61, by decide⟩ 23 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 23 (transLenTr ⟨61, by decide⟩ 23 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 23 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_23.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_61_61_24 (hp : 24 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 61 []).length)
    (hq : (normIsRep.getD 61 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 24 hp)
        (rowE2 (⟨61, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 24 (transLenTr ⟨61, by decide⟩ 24 hp))
        (rowE1 (⟨61, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨61, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨61, by decide⟩ (listedAt ⟨61, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 24 (transLenTr ⟨61, by decide⟩ 24 hp)) T61_61
      hfix61_61 hinj61_61 hcardT61_61
      (fun i => conj_mem_of_fixedPoints _ _ (T61_61 i) (hfix61_61 i) _)
      ⟨61, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨61, by decide⟩ (Q2.listedAt ⟨61, by decide⟩
        (alnCheck_rep ⟨61, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 24 hp) Q2.T61_61_2 Q2.hfix61_61_2 Q2.hinj61_61_2
      Q2.hcardT61_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T61_61_2 i) (Q2.hfix61_61_2 i) _)
      colCert_61_61_24.hD ?_).symm
  rw [alnId_61 j hj]


theorem leaf_62_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T62_7
      hfix62_7 hinj62_7 hcardT62_7
      (fun i => conj_mem_of_fixedPoints _ _ (T62_7 i) (hfix62_7 i) _)
      ⟨62, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T62_7_2 Q2.hfix62_7_2 Q2.hinj62_7_2
      Q2.hcardT62_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_7_2 i) (Q2.hfix62_7_2 i) _)
      colCert_62_7_0.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T62_7
      hfix62_7 hinj62_7 hcardT62_7
      (fun i => conj_mem_of_fixedPoints _ _ (T62_7 i) (hfix62_7 i) _)
      ⟨62, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T62_7_2 Q2.hfix62_7_2 Q2.hinj62_7_2
      Q2.hcardT62_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_7_2 i) (Q2.hfix62_7_2 i) _)
      colCert_62_7_1.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T62_7
      hfix62_7 hinj62_7 hcardT62_7
      (fun i => conj_mem_of_fixedPoints _ _ (T62_7 i) (hfix62_7 i) _)
      ⟨62, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T62_7_2 Q2.hfix62_7_2 Q2.hinj62_7_2
      Q2.hcardT62_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_7_2 i) (Q2.hfix62_7_2 i) _)
      colCert_62_7_2.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T62_7
      hfix62_7 hinj62_7 hcardT62_7
      (fun i => conj_mem_of_fixedPoints _ _ (T62_7 i) (hfix62_7 i) _)
      ⟨62, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T62_7_2 Q2.hfix62_7_2 Q2.hinj62_7_2
      Q2.hcardT62_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_7_2 i) (Q2.hfix62_7_2 i) _)
      colCert_62_7_3.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T62_7
      hfix62_7 hinj62_7 hcardT62_7
      (fun i => conj_mem_of_fixedPoints _ _ (T62_7 i) (hfix62_7 i) _)
      ⟨62, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T62_7_2 Q2.hfix62_7_2 Q2.hinj62_7_2
      Q2.hcardT62_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_7_2 i) (Q2.hfix62_7_2 i) _)
      colCert_62_7_4.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T62_12
      hfix62_12 hinj62_12 hcardT62_12
      (fun i => conj_mem_of_fixedPoints _ _ (T62_12 i) (hfix62_12 i) _)
      ⟨62, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T62_12_2 Q2.hfix62_12_2 Q2.hinj62_12_2
      Q2.hcardT62_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_12_2 i) (Q2.hfix62_12_2 i) _)
      colCert_62_12_0.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T62_12
      hfix62_12 hinj62_12 hcardT62_12
      (fun i => conj_mem_of_fixedPoints _ _ (T62_12 i) (hfix62_12 i) _)
      ⟨62, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T62_12_2 Q2.hfix62_12_2 Q2.hinj62_12_2
      Q2.hcardT62_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_12_2 i) (Q2.hfix62_12_2 i) _)
      colCert_62_12_1.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T62_12
      hfix62_12 hinj62_12 hcardT62_12
      (fun i => conj_mem_of_fixedPoints _ _ (T62_12 i) (hfix62_12 i) _)
      ⟨62, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T62_12_2 Q2.hfix62_12_2 Q2.hinj62_12_2
      Q2.hcardT62_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_12_2 i) (Q2.hfix62_12_2 i) _)
      colCert_62_12_2.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T62_12
      hfix62_12 hinj62_12 hcardT62_12
      (fun i => conj_mem_of_fixedPoints _ _ (T62_12 i) (hfix62_12 i) _)
      ⟨62, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T62_12_2 Q2.hfix62_12_2 Q2.hinj62_12_2
      Q2.hcardT62_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_12_2 i) (Q2.hfix62_12_2 i) _)
      colCert_62_12_3.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T62_12
      hfix62_12 hinj62_12 hcardT62_12
      (fun i => conj_mem_of_fixedPoints _ _ (T62_12 i) (hfix62_12 i) _)
      ⟨62, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T62_12_2 Q2.hfix62_12_2 Q2.hinj62_12_2
      Q2.hcardT62_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_12_2 i) (Q2.hfix62_12_2 i) _)
      colCert_62_12_4.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T62_25
      hfix62_25 hinj62_25 hcardT62_25
      (fun i => conj_mem_of_fixedPoints _ _ (T62_25 i) (hfix62_25 i) _)
      ⟨62, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T62_25_2 Q2.hfix62_25_2 Q2.hinj62_25_2
      Q2.hcardT62_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_25_2 i) (Q2.hfix62_25_2 i) _)
      colCert_62_25_0.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T62_25
      hfix62_25 hinj62_25 hcardT62_25
      (fun i => conj_mem_of_fixedPoints _ _ (T62_25 i) (hfix62_25 i) _)
      ⟨62, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T62_25_2 Q2.hfix62_25_2 Q2.hinj62_25_2
      Q2.hcardT62_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_25_2 i) (Q2.hfix62_25_2 i) _)
      colCert_62_25_1.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T62_25
      hfix62_25 hinj62_25 hcardT62_25
      (fun i => conj_mem_of_fixedPoints _ _ (T62_25 i) (hfix62_25 i) _)
      ⟨62, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T62_25_2 Q2.hfix62_25_2 Q2.hinj62_25_2
      Q2.hcardT62_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_25_2 i) (Q2.hfix62_25_2 i) _)
      colCert_62_25_2.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T62_25
      hfix62_25 hinj62_25 hcardT62_25
      (fun i => conj_mem_of_fixedPoints _ _ (T62_25 i) (hfix62_25 i) _)
      ⟨62, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T62_25_2 Q2.hfix62_25_2 Q2.hinj62_25_2
      Q2.hcardT62_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_25_2 i) (Q2.hfix62_25_2 i) _)
      colCert_62_25_3.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T62_25
      hfix62_25 hinj62_25 hcardT62_25
      (fun i => conj_mem_of_fixedPoints _ _ (T62_25 i) (hfix62_25 i) _)
      ⟨62, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T62_25_2 Q2.hfix62_25_2 Q2.hinj62_25_2
      Q2.hcardT62_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_25_2 i) (Q2.hfix62_25_2 i) _)
      colCert_62_25_4.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T62_25
      hfix62_25 hinj62_25 hcardT62_25
      (fun i => conj_mem_of_fixedPoints _ _ (T62_25 i) (hfix62_25 i) _)
      ⟨62, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T62_25_2 Q2.hfix62_25_2 Q2.hinj62_25_2
      Q2.hcardT62_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_25_2 i) (Q2.hfix62_25_2 i) _)
      colCert_62_25_5.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T62_25
      hfix62_25 hinj62_25 hcardT62_25
      (fun i => conj_mem_of_fixedPoints _ _ (T62_25 i) (hfix62_25 i) _)
      ⟨62, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T62_25_2 Q2.hfix62_25_2 Q2.hinj62_25_2
      Q2.hcardT62_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_25_2 i) (Q2.hfix62_25_2 i) _)
      colCert_62_25_10.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T62_25
      hfix62_25 hinj62_25 hcardT62_25
      (fun i => conj_mem_of_fixedPoints _ _ (T62_25 i) (hfix62_25 i) _)
      ⟨62, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T62_25_2 Q2.hfix62_25_2 Q2.hinj62_25_2
      Q2.hcardT62_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_25_2 i) (Q2.hfix62_25_2 i) _)
      colCert_62_25_15.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T62_25
      hfix62_25 hinj62_25 hcardT62_25
      (fun i => conj_mem_of_fixedPoints _ _ (T62_25 i) (hfix62_25 i) _)
      ⟨62, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T62_25_2 Q2.hfix62_25_2 Q2.hinj62_25_2
      Q2.hcardT62_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_25_2 i) (Q2.hfix62_25_2 i) _)
      colCert_62_25_20.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T62_29
      hfix62_29 hinj62_29 hcardT62_29
      (fun i => conj_mem_of_fixedPoints _ _ (T62_29 i) (hfix62_29 i) _)
      ⟨62, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T62_29_2 Q2.hfix62_29_2 Q2.hinj62_29_2
      Q2.hcardT62_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_29_2 i) (Q2.hfix62_29_2 i) _)
      colCert_62_29_0.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T62_29
      hfix62_29 hinj62_29 hcardT62_29
      (fun i => conj_mem_of_fixedPoints _ _ (T62_29 i) (hfix62_29 i) _)
      ⟨62, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T62_29_2 Q2.hfix62_29_2 Q2.hinj62_29_2
      Q2.hcardT62_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_29_2 i) (Q2.hfix62_29_2 i) _)
      colCert_62_29_1.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T62_29
      hfix62_29 hinj62_29 hcardT62_29
      (fun i => conj_mem_of_fixedPoints _ _ (T62_29 i) (hfix62_29 i) _)
      ⟨62, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T62_29_2 Q2.hfix62_29_2 Q2.hinj62_29_2
      Q2.hcardT62_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_29_2 i) (Q2.hfix62_29_2 i) _)
      colCert_62_29_2.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T62_29
      hfix62_29 hinj62_29 hcardT62_29
      (fun i => conj_mem_of_fixedPoints _ _ (T62_29 i) (hfix62_29 i) _)
      ⟨62, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T62_29_2 Q2.hfix62_29_2 Q2.hinj62_29_2
      Q2.hcardT62_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_29_2 i) (Q2.hfix62_29_2 i) _)
      colCert_62_29_3.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T62_29
      hfix62_29 hinj62_29 hcardT62_29
      (fun i => conj_mem_of_fixedPoints _ _ (T62_29 i) (hfix62_29 i) _)
      ⟨62, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T62_29_2 Q2.hfix62_29_2 Q2.hinj62_29_2
      Q2.hcardT62_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_29_2 i) (Q2.hfix62_29_2 i) _)
      colCert_62_29_4.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T62_29
      hfix62_29 hinj62_29 hcardT62_29
      (fun i => conj_mem_of_fixedPoints _ _ (T62_29 i) (hfix62_29 i) _)
      ⟨62, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T62_29_2 Q2.hfix62_29_2 Q2.hinj62_29_2
      Q2.hcardT62_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_29_2 i) (Q2.hfix62_29_2 i) _)
      colCert_62_29_5.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T62_29
      hfix62_29 hinj62_29 hcardT62_29
      (fun i => conj_mem_of_fixedPoints _ _ (T62_29 i) (hfix62_29 i) _)
      ⟨62, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T62_29_2 Q2.hfix62_29_2 Q2.hinj62_29_2
      Q2.hcardT62_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_29_2 i) (Q2.hfix62_29_2 i) _)
      colCert_62_29_10.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T62_29
      hfix62_29 hinj62_29 hcardT62_29
      (fun i => conj_mem_of_fixedPoints _ _ (T62_29 i) (hfix62_29 i) _)
      ⟨62, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T62_29_2 Q2.hfix62_29_2 Q2.hinj62_29_2
      Q2.hcardT62_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_29_2 i) (Q2.hfix62_29_2 i) _)
      colCert_62_29_15.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T62_29
      hfix62_29 hinj62_29 hcardT62_29
      (fun i => conj_mem_of_fixedPoints _ _ (T62_29 i) (hfix62_29 i) _)
      ⟨62, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T62_29_2 Q2.hfix62_29_2 Q2.hinj62_29_2
      Q2.hcardT62_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_29_2 i) (Q2.hfix62_29_2 i) _)
      colCert_62_29_20.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T62_34
      hfix62_34 hinj62_34 hcardT62_34
      (fun i => conj_mem_of_fixedPoints _ _ (T62_34 i) (hfix62_34 i) _)
      ⟨62, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T62_34_2 Q2.hfix62_34_2 Q2.hinj62_34_2
      Q2.hcardT62_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_34_2 i) (Q2.hfix62_34_2 i) _)
      colCert_62_34_0.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T62_34
      hfix62_34 hinj62_34 hcardT62_34
      (fun i => conj_mem_of_fixedPoints _ _ (T62_34 i) (hfix62_34 i) _)
      ⟨62, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T62_34_2 Q2.hfix62_34_2 Q2.hinj62_34_2
      Q2.hcardT62_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_34_2 i) (Q2.hfix62_34_2 i) _)
      colCert_62_34_1.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T62_34
      hfix62_34 hinj62_34 hcardT62_34
      (fun i => conj_mem_of_fixedPoints _ _ (T62_34 i) (hfix62_34 i) _)
      ⟨62, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T62_34_2 Q2.hfix62_34_2 Q2.hinj62_34_2
      Q2.hcardT62_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_34_2 i) (Q2.hfix62_34_2 i) _)
      colCert_62_34_2.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T62_34
      hfix62_34 hinj62_34 hcardT62_34
      (fun i => conj_mem_of_fixedPoints _ _ (T62_34 i) (hfix62_34 i) _)
      ⟨62, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T62_34_2 Q2.hfix62_34_2 Q2.hinj62_34_2
      Q2.hcardT62_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_34_2 i) (Q2.hfix62_34_2 i) _)
      colCert_62_34_3.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T62_34
      hfix62_34 hinj62_34 hcardT62_34
      (fun i => conj_mem_of_fixedPoints _ _ (T62_34 i) (hfix62_34 i) _)
      ⟨62, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T62_34_2 Q2.hfix62_34_2 Q2.hinj62_34_2
      Q2.hcardT62_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_34_2 i) (Q2.hfix62_34_2 i) _)
      colCert_62_34_4.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T62_34
      hfix62_34 hinj62_34 hcardT62_34
      (fun i => conj_mem_of_fixedPoints _ _ (T62_34 i) (hfix62_34 i) _)
      ⟨62, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T62_34_2 Q2.hfix62_34_2 Q2.hinj62_34_2
      Q2.hcardT62_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_34_2 i) (Q2.hfix62_34_2 i) _)
      colCert_62_34_5.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T62_34
      hfix62_34 hinj62_34 hcardT62_34
      (fun i => conj_mem_of_fixedPoints _ _ (T62_34 i) (hfix62_34 i) _)
      ⟨62, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T62_34_2 Q2.hfix62_34_2 Q2.hinj62_34_2
      Q2.hcardT62_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_34_2 i) (Q2.hfix62_34_2 i) _)
      colCert_62_34_10.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T62_34
      hfix62_34 hinj62_34 hcardT62_34
      (fun i => conj_mem_of_fixedPoints _ _ (T62_34 i) (hfix62_34 i) _)
      ⟨62, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T62_34_2 Q2.hfix62_34_2 Q2.hinj62_34_2
      Q2.hcardT62_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_34_2 i) (Q2.hfix62_34_2 i) _)
      colCert_62_34_15.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T62_34
      hfix62_34 hinj62_34 hcardT62_34
      (fun i => conj_mem_of_fixedPoints _ _ (T62_34 i) (hfix62_34 i) _)
      ⟨62, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T62_34_2 Q2.hfix62_34_2 Q2.hinj62_34_2
      Q2.hcardT62_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_34_2 i) (Q2.hfix62_34_2 i) _)
      colCert_62_34_20.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T62_39
      hfix62_39 hinj62_39 hcardT62_39
      (fun i => conj_mem_of_fixedPoints _ _ (T62_39 i) (hfix62_39 i) _)
      ⟨62, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T62_39_2 Q2.hfix62_39_2 Q2.hinj62_39_2
      Q2.hcardT62_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_39_2 i) (Q2.hfix62_39_2 i) _)
      colCert_62_39_0.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T62_39
      hfix62_39 hinj62_39 hcardT62_39
      (fun i => conj_mem_of_fixedPoints _ _ (T62_39 i) (hfix62_39 i) _)
      ⟨62, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T62_39_2 Q2.hfix62_39_2 Q2.hinj62_39_2
      Q2.hcardT62_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_39_2 i) (Q2.hfix62_39_2 i) _)
      colCert_62_39_1.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T62_39
      hfix62_39 hinj62_39 hcardT62_39
      (fun i => conj_mem_of_fixedPoints _ _ (T62_39 i) (hfix62_39 i) _)
      ⟨62, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T62_39_2 Q2.hfix62_39_2 Q2.hinj62_39_2
      Q2.hcardT62_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_39_2 i) (Q2.hfix62_39_2 i) _)
      colCert_62_39_2.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T62_39
      hfix62_39 hinj62_39 hcardT62_39
      (fun i => conj_mem_of_fixedPoints _ _ (T62_39 i) (hfix62_39 i) _)
      ⟨62, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T62_39_2 Q2.hfix62_39_2 Q2.hinj62_39_2
      Q2.hcardT62_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_39_2 i) (Q2.hfix62_39_2 i) _)
      colCert_62_39_3.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T62_39
      hfix62_39 hinj62_39 hcardT62_39
      (fun i => conj_mem_of_fixedPoints _ _ (T62_39 i) (hfix62_39 i) _)
      ⟨62, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T62_39_2 Q2.hfix62_39_2 Q2.hinj62_39_2
      Q2.hcardT62_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_39_2 i) (Q2.hfix62_39_2 i) _)
      colCert_62_39_4.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T62_39
      hfix62_39 hinj62_39 hcardT62_39
      (fun i => conj_mem_of_fixedPoints _ _ (T62_39 i) (hfix62_39 i) _)
      ⟨62, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T62_39_2 Q2.hfix62_39_2 Q2.hinj62_39_2
      Q2.hcardT62_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_39_2 i) (Q2.hfix62_39_2 i) _)
      colCert_62_39_5.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T62_39
      hfix62_39 hinj62_39 hcardT62_39
      (fun i => conj_mem_of_fixedPoints _ _ (T62_39 i) (hfix62_39 i) _)
      ⟨62, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T62_39_2 Q2.hfix62_39_2 Q2.hinj62_39_2
      Q2.hcardT62_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_39_2 i) (Q2.hfix62_39_2 i) _)
      colCert_62_39_10.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T62_39
      hfix62_39 hinj62_39 hcardT62_39
      (fun i => conj_mem_of_fixedPoints _ _ (T62_39 i) (hfix62_39 i) _)
      ⟨62, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T62_39_2 Q2.hfix62_39_2 Q2.hinj62_39_2
      Q2.hcardT62_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_39_2 i) (Q2.hfix62_39_2 i) _)
      colCert_62_39_15.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T62_39
      hfix62_39 hinj62_39 hcardT62_39
      (fun i => conj_mem_of_fixedPoints _ _ (T62_39 i) (hfix62_39 i) _)
      ⟨62, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T62_39_2 Q2.hfix62_39_2 Q2.hinj62_39_2
      Q2.hcardT62_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_39_2 i) (Q2.hfix62_39_2 i) _)
      colCert_62_39_20.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T62_44
      hfix62_44 hinj62_44 hcardT62_44
      (fun i => conj_mem_of_fixedPoints _ _ (T62_44 i) (hfix62_44 i) _)
      ⟨62, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T62_44_2 Q2.hfix62_44_2 Q2.hinj62_44_2
      Q2.hcardT62_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_44_2 i) (Q2.hfix62_44_2 i) _)
      colCert_62_44_0.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T62_44
      hfix62_44 hinj62_44 hcardT62_44
      (fun i => conj_mem_of_fixedPoints _ _ (T62_44 i) (hfix62_44 i) _)
      ⟨62, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T62_44_2 Q2.hfix62_44_2 Q2.hinj62_44_2
      Q2.hcardT62_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_44_2 i) (Q2.hfix62_44_2 i) _)
      colCert_62_44_1.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T62_44
      hfix62_44 hinj62_44 hcardT62_44
      (fun i => conj_mem_of_fixedPoints _ _ (T62_44 i) (hfix62_44 i) _)
      ⟨62, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T62_44_2 Q2.hfix62_44_2 Q2.hinj62_44_2
      Q2.hcardT62_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_44_2 i) (Q2.hfix62_44_2 i) _)
      colCert_62_44_2.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T62_44
      hfix62_44 hinj62_44 hcardT62_44
      (fun i => conj_mem_of_fixedPoints _ _ (T62_44 i) (hfix62_44 i) _)
      ⟨62, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T62_44_2 Q2.hfix62_44_2 Q2.hinj62_44_2
      Q2.hcardT62_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_44_2 i) (Q2.hfix62_44_2 i) _)
      colCert_62_44_3.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T62_44
      hfix62_44 hinj62_44 hcardT62_44
      (fun i => conj_mem_of_fixedPoints _ _ (T62_44 i) (hfix62_44 i) _)
      ⟨62, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T62_44_2 Q2.hfix62_44_2 Q2.hinj62_44_2
      Q2.hcardT62_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_44_2 i) (Q2.hfix62_44_2 i) _)
      colCert_62_44_4.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T62_44
      hfix62_44 hinj62_44 hcardT62_44
      (fun i => conj_mem_of_fixedPoints _ _ (T62_44 i) (hfix62_44 i) _)
      ⟨62, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T62_44_2 Q2.hfix62_44_2 Q2.hinj62_44_2
      Q2.hcardT62_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_44_2 i) (Q2.hfix62_44_2 i) _)
      colCert_62_44_5.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T62_44
      hfix62_44 hinj62_44 hcardT62_44
      (fun i => conj_mem_of_fixedPoints _ _ (T62_44 i) (hfix62_44 i) _)
      ⟨62, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T62_44_2 Q2.hfix62_44_2 Q2.hinj62_44_2
      Q2.hcardT62_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_44_2 i) (Q2.hfix62_44_2 i) _)
      colCert_62_44_10.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T62_44
      hfix62_44 hinj62_44 hcardT62_44
      (fun i => conj_mem_of_fixedPoints _ _ (T62_44 i) (hfix62_44 i) _)
      ⟨62, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T62_44_2 Q2.hfix62_44_2 Q2.hinj62_44_2
      Q2.hcardT62_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_44_2 i) (Q2.hfix62_44_2 i) _)
      colCert_62_44_15.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T62_44
      hfix62_44 hinj62_44 hcardT62_44
      (fun i => conj_mem_of_fixedPoints _ _ (T62_44 i) (hfix62_44 i) _)
      ⟨62, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T62_44_2 Q2.hfix62_44_2 Q2.hinj62_44_2
      Q2.hcardT62_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_44_2 i) (Q2.hfix62_44_2 i) _)
      colCert_62_44_20.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T62_49
      hfix62_49 hinj62_49 hcardT62_49
      (fun i => conj_mem_of_fixedPoints _ _ (T62_49 i) (hfix62_49 i) _)
      ⟨62, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T62_49_2 Q2.hfix62_49_2 Q2.hinj62_49_2
      Q2.hcardT62_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_49_2 i) (Q2.hfix62_49_2 i) _)
      colCert_62_49_0.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T62_49
      hfix62_49 hinj62_49 hcardT62_49
      (fun i => conj_mem_of_fixedPoints _ _ (T62_49 i) (hfix62_49 i) _)
      ⟨62, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T62_49_2 Q2.hfix62_49_2 Q2.hinj62_49_2
      Q2.hcardT62_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_49_2 i) (Q2.hfix62_49_2 i) _)
      colCert_62_49_1.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T62_49
      hfix62_49 hinj62_49 hcardT62_49
      (fun i => conj_mem_of_fixedPoints _ _ (T62_49 i) (hfix62_49 i) _)
      ⟨62, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T62_49_2 Q2.hfix62_49_2 Q2.hinj62_49_2
      Q2.hcardT62_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_49_2 i) (Q2.hfix62_49_2 i) _)
      colCert_62_49_2.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T62_49
      hfix62_49 hinj62_49 hcardT62_49
      (fun i => conj_mem_of_fixedPoints _ _ (T62_49 i) (hfix62_49 i) _)
      ⟨62, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T62_49_2 Q2.hfix62_49_2 Q2.hinj62_49_2
      Q2.hcardT62_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_49_2 i) (Q2.hfix62_49_2 i) _)
      colCert_62_49_3.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T62_49
      hfix62_49 hinj62_49 hcardT62_49
      (fun i => conj_mem_of_fixedPoints _ _ (T62_49 i) (hfix62_49 i) _)
      ⟨62, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T62_49_2 Q2.hfix62_49_2 Q2.hinj62_49_2
      Q2.hcardT62_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_49_2 i) (Q2.hfix62_49_2 i) _)
      colCert_62_49_4.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T62_49
      hfix62_49 hinj62_49 hcardT62_49
      (fun i => conj_mem_of_fixedPoints _ _ (T62_49 i) (hfix62_49 i) _)
      ⟨62, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T62_49_2 Q2.hfix62_49_2 Q2.hinj62_49_2
      Q2.hcardT62_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_49_2 i) (Q2.hfix62_49_2 i) _)
      colCert_62_49_5.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T62_49
      hfix62_49 hinj62_49 hcardT62_49
      (fun i => conj_mem_of_fixedPoints _ _ (T62_49 i) (hfix62_49 i) _)
      ⟨62, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T62_49_2 Q2.hfix62_49_2 Q2.hinj62_49_2
      Q2.hcardT62_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_49_2 i) (Q2.hfix62_49_2 i) _)
      colCert_62_49_10.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T62_49
      hfix62_49 hinj62_49 hcardT62_49
      (fun i => conj_mem_of_fixedPoints _ _ (T62_49 i) (hfix62_49 i) _)
      ⟨62, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T62_49_2 Q2.hfix62_49_2 Q2.hinj62_49_2
      Q2.hcardT62_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_49_2 i) (Q2.hfix62_49_2 i) _)
      colCert_62_49_15.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T62_49
      hfix62_49 hinj62_49 hcardT62_49
      (fun i => conj_mem_of_fixedPoints _ _ (T62_49 i) (hfix62_49 i) _)
      ⟨62, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T62_49_2 Q2.hfix62_49_2 Q2.hinj62_49_2
      Q2.hcardT62_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_49_2 i) (Q2.hfix62_49_2 i) _)
      colCert_62_49_20.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_0 (hp : 0 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 0 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 0 (transLenTr ⟨62, by decide⟩ 0 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 0 (transLenTr ⟨62, by decide⟩ 0 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 0 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_0.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_1 (hp : 1 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 1 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 1 (transLenTr ⟨62, by decide⟩ 1 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 1 (transLenTr ⟨62, by decide⟩ 1 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 1 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_1.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_2 (hp : 2 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 2 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 2 (transLenTr ⟨62, by decide⟩ 2 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 2 (transLenTr ⟨62, by decide⟩ 2 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 2 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_2.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_3 (hp : 3 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 3 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 3 (transLenTr ⟨62, by decide⟩ 3 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 3 (transLenTr ⟨62, by decide⟩ 3 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 3 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_3.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_4 (hp : 4 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 4 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 4 (transLenTr ⟨62, by decide⟩ 4 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 4 (transLenTr ⟨62, by decide⟩ 4 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 4 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_4.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_5 (hp : 5 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 5 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 5 (transLenTr ⟨62, by decide⟩ 5 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 5 (transLenTr ⟨62, by decide⟩ 5 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 5 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_5.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_6 (hp : 6 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 6 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 6 (transLenTr ⟨62, by decide⟩ 6 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 6 (transLenTr ⟨62, by decide⟩ 6 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 6 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_6.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_7 (hp : 7 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 7 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 7 (transLenTr ⟨62, by decide⟩ 7 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 7 (transLenTr ⟨62, by decide⟩ 7 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 7 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_7.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_8 (hp : 8 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 8 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 8 (transLenTr ⟨62, by decide⟩ 8 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 8 (transLenTr ⟨62, by decide⟩ 8 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 8 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_8.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_9 (hp : 9 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 9 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 9 (transLenTr ⟨62, by decide⟩ 9 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 9 (transLenTr ⟨62, by decide⟩ 9 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 9 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_9.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_10 (hp : 10 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 10 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 10 (transLenTr ⟨62, by decide⟩ 10 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 10 (transLenTr ⟨62, by decide⟩ 10 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 10 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_10.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_11 (hp : 11 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 11 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 11 (transLenTr ⟨62, by decide⟩ 11 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 11 (transLenTr ⟨62, by decide⟩ 11 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 11 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_11.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_12 (hp : 12 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 12 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 12 (transLenTr ⟨62, by decide⟩ 12 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 12 (transLenTr ⟨62, by decide⟩ 12 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 12 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_12.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_13 (hp : 13 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 13 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 13 (transLenTr ⟨62, by decide⟩ 13 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 13 (transLenTr ⟨62, by decide⟩ 13 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 13 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_13.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_14 (hp : 14 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 14 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 14 (transLenTr ⟨62, by decide⟩ 14 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 14 (transLenTr ⟨62, by decide⟩ 14 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 14 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_14.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_15 (hp : 15 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 15 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 15 (transLenTr ⟨62, by decide⟩ 15 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 15 (transLenTr ⟨62, by decide⟩ 15 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 15 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_15.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_16 (hp : 16 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 16 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 16 (transLenTr ⟨62, by decide⟩ 16 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 16 (transLenTr ⟨62, by decide⟩ 16 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 16 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_16.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_17 (hp : 17 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 17 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 17 (transLenTr ⟨62, by decide⟩ 17 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 17 (transLenTr ⟨62, by decide⟩ 17 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 17 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_17.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_18 (hp : 18 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 18 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 18 (transLenTr ⟨62, by decide⟩ 18 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 18 (transLenTr ⟨62, by decide⟩ 18 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 18 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_18.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_19 (hp : 19 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 19 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 19 (transLenTr ⟨62, by decide⟩ 19 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 19 (transLenTr ⟨62, by decide⟩ 19 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 19 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_19.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_20 (hp : 20 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 20 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 20 (transLenTr ⟨62, by decide⟩ 20 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 20 (transLenTr ⟨62, by decide⟩ 20 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 20 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_20.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_21 (hp : 21 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 21 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 21 (transLenTr ⟨62, by decide⟩ 21 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 21 (transLenTr ⟨62, by decide⟩ 21 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 21 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_21.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_22 (hp : 22 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 22 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 22 (transLenTr ⟨62, by decide⟩ 22 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 22 (transLenTr ⟨62, by decide⟩ 22 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 22 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_22.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_23 (hp : 23 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 23 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 23 (transLenTr ⟨62, by decide⟩ 23 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 23 (transLenTr ⟨62, by decide⟩ 23 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 23 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_23.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_62_62_24 (hp : 24 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 62 []).length)
    (hq : (normIsRep.getD 62 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 24 hp)
        (rowE2 (⟨62, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 24 (transLenTr ⟨62, by decide⟩ 24 hp))
        (rowE1 (⟨62, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨62, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨62, by decide⟩ (listedAt ⟨62, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 24 (transLenTr ⟨62, by decide⟩ 24 hp)) T62_62
      hfix62_62 hinj62_62 hcardT62_62
      (fun i => conj_mem_of_fixedPoints _ _ (T62_62 i) (hfix62_62 i) _)
      ⟨62, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨62, by decide⟩ (Q2.listedAt ⟨62, by decide⟩
        (alnCheck_rep ⟨62, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 24 hp) Q2.T62_62_2 Q2.hfix62_62_2 Q2.hinj62_62_2
      Q2.hcardT62_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T62_62_2 i) (Q2.hfix62_62_2 i) _)
      colCert_62_62_24.hD ?_).symm
  rw [alnId_62 j hj]


theorem leaf_63_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T63_6
      hfix63_6 hinj63_6 hcardT63_6
      (fun i => conj_mem_of_fixedPoints _ _ (T63_6 i) (hfix63_6 i) _)
      ⟨63, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T63_6_2 Q2.hfix63_6_2 Q2.hinj63_6_2
      Q2.hcardT63_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_6_2 i) (Q2.hfix63_6_2 i) _)
      colCert_63_6_0.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T63_6
      hfix63_6 hinj63_6 hcardT63_6
      (fun i => conj_mem_of_fixedPoints _ _ (T63_6 i) (hfix63_6 i) _)
      ⟨63, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T63_6_2 Q2.hfix63_6_2 Q2.hinj63_6_2
      Q2.hcardT63_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_6_2 i) (Q2.hfix63_6_2 i) _)
      colCert_63_6_1.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T63_6
      hfix63_6 hinj63_6 hcardT63_6
      (fun i => conj_mem_of_fixedPoints _ _ (T63_6 i) (hfix63_6 i) _)
      ⟨63, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T63_6_2 Q2.hfix63_6_2 Q2.hinj63_6_2
      Q2.hcardT63_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_6_2 i) (Q2.hfix63_6_2 i) _)
      colCert_63_6_2.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T63_6
      hfix63_6 hinj63_6 hcardT63_6
      (fun i => conj_mem_of_fixedPoints _ _ (T63_6 i) (hfix63_6 i) _)
      ⟨63, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T63_6_2 Q2.hfix63_6_2 Q2.hinj63_6_2
      Q2.hcardT63_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_6_2 i) (Q2.hfix63_6_2 i) _)
      colCert_63_6_3.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T63_6
      hfix63_6 hinj63_6 hcardT63_6
      (fun i => conj_mem_of_fixedPoints _ _ (T63_6 i) (hfix63_6 i) _)
      ⟨63, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T63_6_2 Q2.hfix63_6_2 Q2.hinj63_6_2
      Q2.hcardT63_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_6_2 i) (Q2.hfix63_6_2 i) _)
      colCert_63_6_4.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T63_12
      hfix63_12 hinj63_12 hcardT63_12
      (fun i => conj_mem_of_fixedPoints _ _ (T63_12 i) (hfix63_12 i) _)
      ⟨63, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T63_12_2 Q2.hfix63_12_2 Q2.hinj63_12_2
      Q2.hcardT63_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_12_2 i) (Q2.hfix63_12_2 i) _)
      colCert_63_12_0.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T63_12
      hfix63_12 hinj63_12 hcardT63_12
      (fun i => conj_mem_of_fixedPoints _ _ (T63_12 i) (hfix63_12 i) _)
      ⟨63, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T63_12_2 Q2.hfix63_12_2 Q2.hinj63_12_2
      Q2.hcardT63_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_12_2 i) (Q2.hfix63_12_2 i) _)
      colCert_63_12_1.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T63_12
      hfix63_12 hinj63_12 hcardT63_12
      (fun i => conj_mem_of_fixedPoints _ _ (T63_12 i) (hfix63_12 i) _)
      ⟨63, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T63_12_2 Q2.hfix63_12_2 Q2.hinj63_12_2
      Q2.hcardT63_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_12_2 i) (Q2.hfix63_12_2 i) _)
      colCert_63_12_2.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T63_12
      hfix63_12 hinj63_12 hcardT63_12
      (fun i => conj_mem_of_fixedPoints _ _ (T63_12 i) (hfix63_12 i) _)
      ⟨63, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T63_12_2 Q2.hfix63_12_2 Q2.hinj63_12_2
      Q2.hcardT63_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_12_2 i) (Q2.hfix63_12_2 i) _)
      colCert_63_12_3.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T63_12
      hfix63_12 hinj63_12 hcardT63_12
      (fun i => conj_mem_of_fixedPoints _ _ (T63_12 i) (hfix63_12 i) _)
      ⟨63, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T63_12_2 Q2.hfix63_12_2 Q2.hinj63_12_2
      Q2.hcardT63_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_12_2 i) (Q2.hfix63_12_2 i) _)
      colCert_63_12_4.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T63_24
      hfix63_24 hinj63_24 hcardT63_24
      (fun i => conj_mem_of_fixedPoints _ _ (T63_24 i) (hfix63_24 i) _)
      ⟨63, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T63_24_2 Q2.hfix63_24_2 Q2.hinj63_24_2
      Q2.hcardT63_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_24_2 i) (Q2.hfix63_24_2 i) _)
      colCert_63_24_0.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T63_24
      hfix63_24 hinj63_24 hcardT63_24
      (fun i => conj_mem_of_fixedPoints _ _ (T63_24 i) (hfix63_24 i) _)
      ⟨63, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T63_24_2 Q2.hfix63_24_2 Q2.hinj63_24_2
      Q2.hcardT63_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_24_2 i) (Q2.hfix63_24_2 i) _)
      colCert_63_24_1.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T63_24
      hfix63_24 hinj63_24 hcardT63_24
      (fun i => conj_mem_of_fixedPoints _ _ (T63_24 i) (hfix63_24 i) _)
      ⟨63, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T63_24_2 Q2.hfix63_24_2 Q2.hinj63_24_2
      Q2.hcardT63_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_24_2 i) (Q2.hfix63_24_2 i) _)
      colCert_63_24_2.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T63_24
      hfix63_24 hinj63_24 hcardT63_24
      (fun i => conj_mem_of_fixedPoints _ _ (T63_24 i) (hfix63_24 i) _)
      ⟨63, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T63_24_2 Q2.hfix63_24_2 Q2.hinj63_24_2
      Q2.hcardT63_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_24_2 i) (Q2.hfix63_24_2 i) _)
      colCert_63_24_3.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T63_24
      hfix63_24 hinj63_24 hcardT63_24
      (fun i => conj_mem_of_fixedPoints _ _ (T63_24 i) (hfix63_24 i) _)
      ⟨63, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T63_24_2 Q2.hfix63_24_2 Q2.hinj63_24_2
      Q2.hcardT63_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_24_2 i) (Q2.hfix63_24_2 i) _)
      colCert_63_24_4.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T63_24
      hfix63_24 hinj63_24 hcardT63_24
      (fun i => conj_mem_of_fixedPoints _ _ (T63_24 i) (hfix63_24 i) _)
      ⟨63, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T63_24_2 Q2.hfix63_24_2 Q2.hinj63_24_2
      Q2.hcardT63_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_24_2 i) (Q2.hfix63_24_2 i) _)
      colCert_63_24_5.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T63_24
      hfix63_24 hinj63_24 hcardT63_24
      (fun i => conj_mem_of_fixedPoints _ _ (T63_24 i) (hfix63_24 i) _)
      ⟨63, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T63_24_2 Q2.hfix63_24_2 Q2.hinj63_24_2
      Q2.hcardT63_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_24_2 i) (Q2.hfix63_24_2 i) _)
      colCert_63_24_10.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T63_24
      hfix63_24 hinj63_24 hcardT63_24
      (fun i => conj_mem_of_fixedPoints _ _ (T63_24 i) (hfix63_24 i) _)
      ⟨63, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T63_24_2 Q2.hfix63_24_2 Q2.hinj63_24_2
      Q2.hcardT63_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_24_2 i) (Q2.hfix63_24_2 i) _)
      colCert_63_24_15.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T63_24
      hfix63_24 hinj63_24 hcardT63_24
      (fun i => conj_mem_of_fixedPoints _ _ (T63_24 i) (hfix63_24 i) _)
      ⟨63, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T63_24_2 Q2.hfix63_24_2 Q2.hinj63_24_2
      Q2.hcardT63_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_24_2 i) (Q2.hfix63_24_2 i) _)
      colCert_63_24_20.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T63_29
      hfix63_29 hinj63_29 hcardT63_29
      (fun i => conj_mem_of_fixedPoints _ _ (T63_29 i) (hfix63_29 i) _)
      ⟨63, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T63_29_2 Q2.hfix63_29_2 Q2.hinj63_29_2
      Q2.hcardT63_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_29_2 i) (Q2.hfix63_29_2 i) _)
      colCert_63_29_0.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T63_29
      hfix63_29 hinj63_29 hcardT63_29
      (fun i => conj_mem_of_fixedPoints _ _ (T63_29 i) (hfix63_29 i) _)
      ⟨63, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T63_29_2 Q2.hfix63_29_2 Q2.hinj63_29_2
      Q2.hcardT63_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_29_2 i) (Q2.hfix63_29_2 i) _)
      colCert_63_29_1.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T63_29
      hfix63_29 hinj63_29 hcardT63_29
      (fun i => conj_mem_of_fixedPoints _ _ (T63_29 i) (hfix63_29 i) _)
      ⟨63, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T63_29_2 Q2.hfix63_29_2 Q2.hinj63_29_2
      Q2.hcardT63_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_29_2 i) (Q2.hfix63_29_2 i) _)
      colCert_63_29_2.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T63_29
      hfix63_29 hinj63_29 hcardT63_29
      (fun i => conj_mem_of_fixedPoints _ _ (T63_29 i) (hfix63_29 i) _)
      ⟨63, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T63_29_2 Q2.hfix63_29_2 Q2.hinj63_29_2
      Q2.hcardT63_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_29_2 i) (Q2.hfix63_29_2 i) _)
      colCert_63_29_3.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T63_29
      hfix63_29 hinj63_29 hcardT63_29
      (fun i => conj_mem_of_fixedPoints _ _ (T63_29 i) (hfix63_29 i) _)
      ⟨63, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T63_29_2 Q2.hfix63_29_2 Q2.hinj63_29_2
      Q2.hcardT63_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_29_2 i) (Q2.hfix63_29_2 i) _)
      colCert_63_29_4.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T63_29
      hfix63_29 hinj63_29 hcardT63_29
      (fun i => conj_mem_of_fixedPoints _ _ (T63_29 i) (hfix63_29 i) _)
      ⟨63, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T63_29_2 Q2.hfix63_29_2 Q2.hinj63_29_2
      Q2.hcardT63_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_29_2 i) (Q2.hfix63_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T63_29 = colFn colCertDiv_63_29_5.D1 (m := 5) from colCertDiv_63_29_5.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 5 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T63_29_2 = colFn colCertDiv_63_29_5.D2 (m := 5) from colCertDiv_63_29_5.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_29_5_match


theorem leaf_63_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T63_29
      hfix63_29 hinj63_29 hcardT63_29
      (fun i => conj_mem_of_fixedPoints _ _ (T63_29 i) (hfix63_29 i) _)
      ⟨63, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T63_29_2 Q2.hfix63_29_2 Q2.hinj63_29_2
      Q2.hcardT63_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_29_2 i) (Q2.hfix63_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T63_29 = colFn colCertDiv_63_29_10.D1 (m := 5) from colCertDiv_63_29_10.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 10 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T63_29_2 = colFn colCertDiv_63_29_10.D2 (m := 5) from colCertDiv_63_29_10.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_29_10_match


theorem leaf_63_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T63_29
      hfix63_29 hinj63_29 hcardT63_29
      (fun i => conj_mem_of_fixedPoints _ _ (T63_29 i) (hfix63_29 i) _)
      ⟨63, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T63_29_2 Q2.hfix63_29_2 Q2.hinj63_29_2
      Q2.hcardT63_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_29_2 i) (Q2.hfix63_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T63_29 = colFn colCertDiv_63_29_15.D1 (m := 5) from colCertDiv_63_29_15.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 15 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T63_29_2 = colFn colCertDiv_63_29_15.D2 (m := 5) from colCertDiv_63_29_15.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_29_15_match


theorem leaf_63_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T63_29
      hfix63_29 hinj63_29 hcardT63_29
      (fun i => conj_mem_of_fixedPoints _ _ (T63_29 i) (hfix63_29 i) _)
      ⟨63, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T63_29_2 Q2.hfix63_29_2 Q2.hinj63_29_2
      Q2.hcardT63_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_29_2 i) (Q2.hfix63_29_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp) : ↥(reps ⟨29, by decide⟩)) : Coordinate 1)
        T63_29 = colFn colCertDiv_63_29_20.D1 (m := 5) from colCertDiv_63_29_20.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨29, by decide⟩ 20 hp : ↥(Q2.reps ⟨29, by decide⟩)) : Coordinate 2)
        Q2.T63_29_2 = colFn colCertDiv_63_29_20.D2 (m := 5) from colCertDiv_63_29_20.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_29_20_match


theorem leaf_63_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T63_34
      hfix63_34 hinj63_34 hcardT63_34
      (fun i => conj_mem_of_fixedPoints _ _ (T63_34 i) (hfix63_34 i) _)
      ⟨63, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T63_34_2 Q2.hfix63_34_2 Q2.hinj63_34_2
      Q2.hcardT63_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_34_2 i) (Q2.hfix63_34_2 i) _)
      colCert_63_34_0.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T63_34
      hfix63_34 hinj63_34 hcardT63_34
      (fun i => conj_mem_of_fixedPoints _ _ (T63_34 i) (hfix63_34 i) _)
      ⟨63, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T63_34_2 Q2.hfix63_34_2 Q2.hinj63_34_2
      Q2.hcardT63_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_34_2 i) (Q2.hfix63_34_2 i) _)
      colCert_63_34_1.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T63_34
      hfix63_34 hinj63_34 hcardT63_34
      (fun i => conj_mem_of_fixedPoints _ _ (T63_34 i) (hfix63_34 i) _)
      ⟨63, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T63_34_2 Q2.hfix63_34_2 Q2.hinj63_34_2
      Q2.hcardT63_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_34_2 i) (Q2.hfix63_34_2 i) _)
      colCert_63_34_2.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T63_34
      hfix63_34 hinj63_34 hcardT63_34
      (fun i => conj_mem_of_fixedPoints _ _ (T63_34 i) (hfix63_34 i) _)
      ⟨63, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T63_34_2 Q2.hfix63_34_2 Q2.hinj63_34_2
      Q2.hcardT63_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_34_2 i) (Q2.hfix63_34_2 i) _)
      colCert_63_34_3.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T63_34
      hfix63_34 hinj63_34 hcardT63_34
      (fun i => conj_mem_of_fixedPoints _ _ (T63_34 i) (hfix63_34 i) _)
      ⟨63, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T63_34_2 Q2.hfix63_34_2 Q2.hinj63_34_2
      Q2.hcardT63_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_34_2 i) (Q2.hfix63_34_2 i) _)
      colCert_63_34_4.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T63_34
      hfix63_34 hinj63_34 hcardT63_34
      (fun i => conj_mem_of_fixedPoints _ _ (T63_34 i) (hfix63_34 i) _)
      ⟨63, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T63_34_2 Q2.hfix63_34_2 Q2.hinj63_34_2
      Q2.hcardT63_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_34_2 i) (Q2.hfix63_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T63_34 = colFn colCertDiv_63_34_5.D1 (m := 5) from colCertDiv_63_34_5.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 5 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T63_34_2 = colFn colCertDiv_63_34_5.D2 (m := 5) from colCertDiv_63_34_5.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_34_5_match


theorem leaf_63_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T63_34
      hfix63_34 hinj63_34 hcardT63_34
      (fun i => conj_mem_of_fixedPoints _ _ (T63_34 i) (hfix63_34 i) _)
      ⟨63, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T63_34_2 Q2.hfix63_34_2 Q2.hinj63_34_2
      Q2.hcardT63_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_34_2 i) (Q2.hfix63_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T63_34 = colFn colCertDiv_63_34_10.D1 (m := 5) from colCertDiv_63_34_10.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 10 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T63_34_2 = colFn colCertDiv_63_34_10.D2 (m := 5) from colCertDiv_63_34_10.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_34_10_match


theorem leaf_63_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T63_34
      hfix63_34 hinj63_34 hcardT63_34
      (fun i => conj_mem_of_fixedPoints _ _ (T63_34 i) (hfix63_34 i) _)
      ⟨63, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T63_34_2 Q2.hfix63_34_2 Q2.hinj63_34_2
      Q2.hcardT63_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_34_2 i) (Q2.hfix63_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T63_34 = colFn colCertDiv_63_34_15.D1 (m := 5) from colCertDiv_63_34_15.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 15 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T63_34_2 = colFn colCertDiv_63_34_15.D2 (m := 5) from colCertDiv_63_34_15.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_34_15_match


theorem leaf_63_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T63_34
      hfix63_34 hinj63_34 hcardT63_34
      (fun i => conj_mem_of_fixedPoints _ _ (T63_34 i) (hfix63_34 i) _)
      ⟨63, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T63_34_2 Q2.hfix63_34_2 Q2.hinj63_34_2
      Q2.hcardT63_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_34_2 i) (Q2.hfix63_34_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp) : ↥(reps ⟨34, by decide⟩)) : Coordinate 1)
        T63_34 = colFn colCertDiv_63_34_20.D1 (m := 5) from colCertDiv_63_34_20.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨34, by decide⟩ 20 hp : ↥(Q2.reps ⟨34, by decide⟩)) : Coordinate 2)
        Q2.T63_34_2 = colFn colCertDiv_63_34_20.D2 (m := 5) from colCertDiv_63_34_20.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_34_20_match


theorem leaf_63_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T63_39
      hfix63_39 hinj63_39 hcardT63_39
      (fun i => conj_mem_of_fixedPoints _ _ (T63_39 i) (hfix63_39 i) _)
      ⟨63, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T63_39_2 Q2.hfix63_39_2 Q2.hinj63_39_2
      Q2.hcardT63_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_39_2 i) (Q2.hfix63_39_2 i) _)
      colCert_63_39_0.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T63_39
      hfix63_39 hinj63_39 hcardT63_39
      (fun i => conj_mem_of_fixedPoints _ _ (T63_39 i) (hfix63_39 i) _)
      ⟨63, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T63_39_2 Q2.hfix63_39_2 Q2.hinj63_39_2
      Q2.hcardT63_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_39_2 i) (Q2.hfix63_39_2 i) _)
      colCert_63_39_1.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T63_39
      hfix63_39 hinj63_39 hcardT63_39
      (fun i => conj_mem_of_fixedPoints _ _ (T63_39 i) (hfix63_39 i) _)
      ⟨63, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T63_39_2 Q2.hfix63_39_2 Q2.hinj63_39_2
      Q2.hcardT63_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_39_2 i) (Q2.hfix63_39_2 i) _)
      colCert_63_39_2.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T63_39
      hfix63_39 hinj63_39 hcardT63_39
      (fun i => conj_mem_of_fixedPoints _ _ (T63_39 i) (hfix63_39 i) _)
      ⟨63, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T63_39_2 Q2.hfix63_39_2 Q2.hinj63_39_2
      Q2.hcardT63_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_39_2 i) (Q2.hfix63_39_2 i) _)
      colCert_63_39_3.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T63_39
      hfix63_39 hinj63_39 hcardT63_39
      (fun i => conj_mem_of_fixedPoints _ _ (T63_39 i) (hfix63_39 i) _)
      ⟨63, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T63_39_2 Q2.hfix63_39_2 Q2.hinj63_39_2
      Q2.hcardT63_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_39_2 i) (Q2.hfix63_39_2 i) _)
      colCert_63_39_4.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T63_39
      hfix63_39 hinj63_39 hcardT63_39
      (fun i => conj_mem_of_fixedPoints _ _ (T63_39 i) (hfix63_39 i) _)
      ⟨63, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T63_39_2 Q2.hfix63_39_2 Q2.hinj63_39_2
      Q2.hcardT63_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_39_2 i) (Q2.hfix63_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T63_39 = colFn colCertDiv_63_39_5.D1 (m := 5) from colCertDiv_63_39_5.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 5 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T63_39_2 = colFn colCertDiv_63_39_5.D2 (m := 5) from colCertDiv_63_39_5.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_39_5_match


theorem leaf_63_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T63_39
      hfix63_39 hinj63_39 hcardT63_39
      (fun i => conj_mem_of_fixedPoints _ _ (T63_39 i) (hfix63_39 i) _)
      ⟨63, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T63_39_2 Q2.hfix63_39_2 Q2.hinj63_39_2
      Q2.hcardT63_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_39_2 i) (Q2.hfix63_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T63_39 = colFn colCertDiv_63_39_10.D1 (m := 5) from colCertDiv_63_39_10.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 10 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T63_39_2 = colFn colCertDiv_63_39_10.D2 (m := 5) from colCertDiv_63_39_10.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_39_10_match


theorem leaf_63_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T63_39
      hfix63_39 hinj63_39 hcardT63_39
      (fun i => conj_mem_of_fixedPoints _ _ (T63_39 i) (hfix63_39 i) _)
      ⟨63, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T63_39_2 Q2.hfix63_39_2 Q2.hinj63_39_2
      Q2.hcardT63_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_39_2 i) (Q2.hfix63_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T63_39 = colFn colCertDiv_63_39_15.D1 (m := 5) from colCertDiv_63_39_15.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 15 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T63_39_2 = colFn colCertDiv_63_39_15.D2 (m := 5) from colCertDiv_63_39_15.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_39_15_match


theorem leaf_63_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T63_39
      hfix63_39 hinj63_39 hcardT63_39
      (fun i => conj_mem_of_fixedPoints _ _ (T63_39 i) (hfix63_39 i) _)
      ⟨63, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T63_39_2 Q2.hfix63_39_2 Q2.hinj63_39_2
      Q2.hcardT63_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_39_2 i) (Q2.hfix63_39_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp) : ↥(reps ⟨39, by decide⟩)) : Coordinate 1)
        T63_39 = colFn colCertDiv_63_39_20.D1 (m := 5) from colCertDiv_63_39_20.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨39, by decide⟩ 20 hp : ↥(Q2.reps ⟨39, by decide⟩)) : Coordinate 2)
        Q2.T63_39_2 = colFn colCertDiv_63_39_20.D2 (m := 5) from colCertDiv_63_39_20.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_39_20_match


theorem leaf_63_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T63_44
      hfix63_44 hinj63_44 hcardT63_44
      (fun i => conj_mem_of_fixedPoints _ _ (T63_44 i) (hfix63_44 i) _)
      ⟨63, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T63_44_2 Q2.hfix63_44_2 Q2.hinj63_44_2
      Q2.hcardT63_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_44_2 i) (Q2.hfix63_44_2 i) _)
      colCert_63_44_0.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T63_44
      hfix63_44 hinj63_44 hcardT63_44
      (fun i => conj_mem_of_fixedPoints _ _ (T63_44 i) (hfix63_44 i) _)
      ⟨63, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T63_44_2 Q2.hfix63_44_2 Q2.hinj63_44_2
      Q2.hcardT63_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_44_2 i) (Q2.hfix63_44_2 i) _)
      colCert_63_44_1.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T63_44
      hfix63_44 hinj63_44 hcardT63_44
      (fun i => conj_mem_of_fixedPoints _ _ (T63_44 i) (hfix63_44 i) _)
      ⟨63, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T63_44_2 Q2.hfix63_44_2 Q2.hinj63_44_2
      Q2.hcardT63_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_44_2 i) (Q2.hfix63_44_2 i) _)
      colCert_63_44_2.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T63_44
      hfix63_44 hinj63_44 hcardT63_44
      (fun i => conj_mem_of_fixedPoints _ _ (T63_44 i) (hfix63_44 i) _)
      ⟨63, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T63_44_2 Q2.hfix63_44_2 Q2.hinj63_44_2
      Q2.hcardT63_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_44_2 i) (Q2.hfix63_44_2 i) _)
      colCert_63_44_3.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T63_44
      hfix63_44 hinj63_44 hcardT63_44
      (fun i => conj_mem_of_fixedPoints _ _ (T63_44 i) (hfix63_44 i) _)
      ⟨63, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T63_44_2 Q2.hfix63_44_2 Q2.hinj63_44_2
      Q2.hcardT63_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_44_2 i) (Q2.hfix63_44_2 i) _)
      colCert_63_44_4.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T63_44
      hfix63_44 hinj63_44 hcardT63_44
      (fun i => conj_mem_of_fixedPoints _ _ (T63_44 i) (hfix63_44 i) _)
      ⟨63, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T63_44_2 Q2.hfix63_44_2 Q2.hinj63_44_2
      Q2.hcardT63_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_44_2 i) (Q2.hfix63_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T63_44 = colFn colCertDiv_63_44_5.D1 (m := 5) from colCertDiv_63_44_5.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 5 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T63_44_2 = colFn colCertDiv_63_44_5.D2 (m := 5) from colCertDiv_63_44_5.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_44_5_match


theorem leaf_63_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T63_44
      hfix63_44 hinj63_44 hcardT63_44
      (fun i => conj_mem_of_fixedPoints _ _ (T63_44 i) (hfix63_44 i) _)
      ⟨63, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T63_44_2 Q2.hfix63_44_2 Q2.hinj63_44_2
      Q2.hcardT63_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_44_2 i) (Q2.hfix63_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T63_44 = colFn colCertDiv_63_44_10.D1 (m := 5) from colCertDiv_63_44_10.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 10 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T63_44_2 = colFn colCertDiv_63_44_10.D2 (m := 5) from colCertDiv_63_44_10.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_44_10_match


theorem leaf_63_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T63_44
      hfix63_44 hinj63_44 hcardT63_44
      (fun i => conj_mem_of_fixedPoints _ _ (T63_44 i) (hfix63_44 i) _)
      ⟨63, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T63_44_2 Q2.hfix63_44_2 Q2.hinj63_44_2
      Q2.hcardT63_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_44_2 i) (Q2.hfix63_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T63_44 = colFn colCertDiv_63_44_15.D1 (m := 5) from colCertDiv_63_44_15.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 15 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T63_44_2 = colFn colCertDiv_63_44_15.D2 (m := 5) from colCertDiv_63_44_15.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_44_15_match


theorem leaf_63_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T63_44
      hfix63_44 hinj63_44 hcardT63_44
      (fun i => conj_mem_of_fixedPoints _ _ (T63_44 i) (hfix63_44 i) _)
      ⟨63, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T63_44_2 Q2.hfix63_44_2 Q2.hinj63_44_2
      Q2.hcardT63_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_44_2 i) (Q2.hfix63_44_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp) : ↥(reps ⟨44, by decide⟩)) : Coordinate 1)
        T63_44 = colFn colCertDiv_63_44_20.D1 (m := 5) from colCertDiv_63_44_20.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨44, by decide⟩ 20 hp : ↥(Q2.reps ⟨44, by decide⟩)) : Coordinate 2)
        Q2.T63_44_2 = colFn colCertDiv_63_44_20.D2 (m := 5) from colCertDiv_63_44_20.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_44_20_match


theorem leaf_63_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T63_49
      hfix63_49 hinj63_49 hcardT63_49
      (fun i => conj_mem_of_fixedPoints _ _ (T63_49 i) (hfix63_49 i) _)
      ⟨63, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T63_49_2 Q2.hfix63_49_2 Q2.hinj63_49_2
      Q2.hcardT63_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_49_2 i) (Q2.hfix63_49_2 i) _)
      colCert_63_49_0.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T63_49
      hfix63_49 hinj63_49 hcardT63_49
      (fun i => conj_mem_of_fixedPoints _ _ (T63_49 i) (hfix63_49 i) _)
      ⟨63, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T63_49_2 Q2.hfix63_49_2 Q2.hinj63_49_2
      Q2.hcardT63_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_49_2 i) (Q2.hfix63_49_2 i) _)
      colCert_63_49_1.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T63_49
      hfix63_49 hinj63_49 hcardT63_49
      (fun i => conj_mem_of_fixedPoints _ _ (T63_49 i) (hfix63_49 i) _)
      ⟨63, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T63_49_2 Q2.hfix63_49_2 Q2.hinj63_49_2
      Q2.hcardT63_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_49_2 i) (Q2.hfix63_49_2 i) _)
      colCert_63_49_2.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T63_49
      hfix63_49 hinj63_49 hcardT63_49
      (fun i => conj_mem_of_fixedPoints _ _ (T63_49 i) (hfix63_49 i) _)
      ⟨63, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T63_49_2 Q2.hfix63_49_2 Q2.hinj63_49_2
      Q2.hcardT63_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_49_2 i) (Q2.hfix63_49_2 i) _)
      colCert_63_49_3.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T63_49
      hfix63_49 hinj63_49 hcardT63_49
      (fun i => conj_mem_of_fixedPoints _ _ (T63_49 i) (hfix63_49 i) _)
      ⟨63, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T63_49_2 Q2.hfix63_49_2 Q2.hinj63_49_2
      Q2.hcardT63_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_49_2 i) (Q2.hfix63_49_2 i) _)
      colCert_63_49_4.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T63_49
      hfix63_49 hinj63_49 hcardT63_49
      (fun i => conj_mem_of_fixedPoints _ _ (T63_49 i) (hfix63_49 i) _)
      ⟨63, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T63_49_2 Q2.hfix63_49_2 Q2.hinj63_49_2
      Q2.hcardT63_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_49_2 i) (Q2.hfix63_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T63_49 = colFn colCertDiv_63_49_5.D1 (m := 5) from colCertDiv_63_49_5.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 5 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T63_49_2 = colFn colCertDiv_63_49_5.D2 (m := 5) from colCertDiv_63_49_5.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_49_5_match


theorem leaf_63_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T63_49
      hfix63_49 hinj63_49 hcardT63_49
      (fun i => conj_mem_of_fixedPoints _ _ (T63_49 i) (hfix63_49 i) _)
      ⟨63, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T63_49_2 Q2.hfix63_49_2 Q2.hinj63_49_2
      Q2.hcardT63_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_49_2 i) (Q2.hfix63_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T63_49 = colFn colCertDiv_63_49_10.D1 (m := 5) from colCertDiv_63_49_10.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 10 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T63_49_2 = colFn colCertDiv_63_49_10.D2 (m := 5) from colCertDiv_63_49_10.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_49_10_match


theorem leaf_63_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T63_49
      hfix63_49 hinj63_49 hcardT63_49
      (fun i => conj_mem_of_fixedPoints _ _ (T63_49 i) (hfix63_49 i) _)
      ⟨63, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T63_49_2 Q2.hfix63_49_2 Q2.hinj63_49_2
      Q2.hcardT63_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_49_2 i) (Q2.hfix63_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T63_49 = colFn colCertDiv_63_49_15.D1 (m := 5) from colCertDiv_63_49_15.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 15 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T63_49_2 = colFn colCertDiv_63_49_15.D2 (m := 5) from colCertDiv_63_49_15.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_49_15_match


theorem leaf_63_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨63, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T63_49
      hfix63_49 hinj63_49 hcardT63_49
      (fun i => conj_mem_of_fixedPoints _ _ (T63_49 i) (hfix63_49 i) _)
      ⟨63, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T63_49_2 Q2.hfix63_49_2 Q2.hinj63_49_2
      Q2.hcardT63_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_49_2 i) (Q2.hfix63_49_2 i) _)
      ?_).symm
  rw [show colData1 (⟨63, by decide⟩ : Fin 148)
        ((colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp) : ↥(reps ⟨49, by decide⟩)) : Coordinate 1)
        T63_49 = colFn colCertDiv_63_49_20.D1 (m := 5) from colCertDiv_63_49_20.bind1,
    show colData2 (⟨63, by decide⟩ : Fin 148)
        ((colE2 ⟨49, by decide⟩ 20 hp : ↥(Q2.reps ⟨49, by decide⟩)) : Coordinate 2)
        Q2.T63_49_2 = colFn colCertDiv_63_49_20.D2 (m := 5) from colCertDiv_63_49_20.bind2]
  rw [alnId_63 j hj]
  exact fastcode_of_div ⟨63, by decide⟩ _ _ _
    ((alnId_63 j hj) ▸ Q2.listedAt (⟨63, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨63, by decide⟩ : Fin 148) hj hq).1) colCertDiv_63_49_20_match


theorem leaf_63_63_0 (hp : 0 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 0 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 0 (transLenTr ⟨63, by decide⟩ 0 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 0 (transLenTr ⟨63, by decide⟩ 0 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 0 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_0.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_1 (hp : 1 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 1 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 1 (transLenTr ⟨63, by decide⟩ 1 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 1 (transLenTr ⟨63, by decide⟩ 1 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 1 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_1.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_2 (hp : 2 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 2 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 2 (transLenTr ⟨63, by decide⟩ 2 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 2 (transLenTr ⟨63, by decide⟩ 2 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 2 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_2.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_3 (hp : 3 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 3 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 3 (transLenTr ⟨63, by decide⟩ 3 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 3 (transLenTr ⟨63, by decide⟩ 3 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 3 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_3.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_4 (hp : 4 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 4 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 4 (transLenTr ⟨63, by decide⟩ 4 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 4 (transLenTr ⟨63, by decide⟩ 4 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 4 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_4.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_5 (hp : 5 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 5 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 5 (transLenTr ⟨63, by decide⟩ 5 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 5 (transLenTr ⟨63, by decide⟩ 5 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 5 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_5.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_6 (hp : 6 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 6 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 6 (transLenTr ⟨63, by decide⟩ 6 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 6 (transLenTr ⟨63, by decide⟩ 6 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 6 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_6.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_7 (hp : 7 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 7 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 7 (transLenTr ⟨63, by decide⟩ 7 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 7 (transLenTr ⟨63, by decide⟩ 7 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 7 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_7.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_8 (hp : 8 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 8 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 8 (transLenTr ⟨63, by decide⟩ 8 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 8 (transLenTr ⟨63, by decide⟩ 8 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 8 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_8.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_9 (hp : 9 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 9 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 9 (transLenTr ⟨63, by decide⟩ 9 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 9 (transLenTr ⟨63, by decide⟩ 9 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 9 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_9.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_10 (hp : 10 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 10 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 10 (transLenTr ⟨63, by decide⟩ 10 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 10 (transLenTr ⟨63, by decide⟩ 10 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 10 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_10.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_11 (hp : 11 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 11 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 11 (transLenTr ⟨63, by decide⟩ 11 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 11 (transLenTr ⟨63, by decide⟩ 11 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 11 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_11.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_12 (hp : 12 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 12 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 12 (transLenTr ⟨63, by decide⟩ 12 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 12 (transLenTr ⟨63, by decide⟩ 12 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 12 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_12.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_13 (hp : 13 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 13 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 13 (transLenTr ⟨63, by decide⟩ 13 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 13 (transLenTr ⟨63, by decide⟩ 13 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 13 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_13.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_14 (hp : 14 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 14 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 14 (transLenTr ⟨63, by decide⟩ 14 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 14 (transLenTr ⟨63, by decide⟩ 14 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 14 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_14.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_15 (hp : 15 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 15 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 15 (transLenTr ⟨63, by decide⟩ 15 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 15 (transLenTr ⟨63, by decide⟩ 15 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 15 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_15.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_16 (hp : 16 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 16 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 16 (transLenTr ⟨63, by decide⟩ 16 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 16 (transLenTr ⟨63, by decide⟩ 16 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 16 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_16.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_17 (hp : 17 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 17 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 17 (transLenTr ⟨63, by decide⟩ 17 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 17 (transLenTr ⟨63, by decide⟩ 17 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 17 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_17.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_18 (hp : 18 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 18 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 18 (transLenTr ⟨63, by decide⟩ 18 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 18 (transLenTr ⟨63, by decide⟩ 18 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 18 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_18.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_19 (hp : 19 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 19 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 19 (transLenTr ⟨63, by decide⟩ 19 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 19 (transLenTr ⟨63, by decide⟩ 19 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 19 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_19.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_20 (hp : 20 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 20 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 20 (transLenTr ⟨63, by decide⟩ 20 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 20 (transLenTr ⟨63, by decide⟩ 20 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 20 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_20.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_21 (hp : 21 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 21 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 21 (transLenTr ⟨63, by decide⟩ 21 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 21 (transLenTr ⟨63, by decide⟩ 21 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 21 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_21.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_22 (hp : 22 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 22 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 22 (transLenTr ⟨63, by decide⟩ 22 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 22 (transLenTr ⟨63, by decide⟩ 22 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 22 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_22.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_23 (hp : 23 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 23 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 23 (transLenTr ⟨63, by decide⟩ 23 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 23 (transLenTr ⟨63, by decide⟩ 23 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 23 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_23.hD ?_).symm
  rw [alnId_63 j hj]


theorem leaf_63_63_24 (hp : 24 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 63 []).length)
    (hq : (normIsRep.getD 63 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 24 hp)
        (rowE2 (⟨63, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 24 (transLenTr ⟨63, by decide⟩ 24 hp))
        (rowE1 (⟨63, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨63, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨63, by decide⟩ (listedAt ⟨63, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 24 (transLenTr ⟨63, by decide⟩ 24 hp)) T63_63
      hfix63_63 hinj63_63 hcardT63_63
      (fun i => conj_mem_of_fixedPoints _ _ (T63_63 i) (hfix63_63 i) _)
      ⟨63, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨63, by decide⟩ (Q2.listedAt ⟨63, by decide⟩
        (alnCheck_rep ⟨63, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 24 hp) Q2.T63_63_2 Q2.hfix63_63_2 Q2.hinj63_63_2
      Q2.hcardT63_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T63_63_2 i) (Q2.hfix63_63_2 i) _)
      colCert_63_63_24.hD ?_).symm
  rw [alnId_63 j hj]


end LeanDring.P5Presentation
