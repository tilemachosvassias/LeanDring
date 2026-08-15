/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C024
import LeanDring.P5.Data.ColCdd.C025
import LeanDring.P5.Data.ColCdd.C026
import LeanDring.P5.Data.ColRestCheap.C115
import LeanDring.P5.Data.ColRestCheap.C116
import LeanDring.P5.Data.ColRestCheap.C117
import LeanDring.P5.Data.EntryK.C044
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C038

/-! # Stage-5 leaves, chunk 50 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_147_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T147_53
      hfix147_53 hinj147_53 hcardT147_53
      (fun i => conj_mem_of_fixedPoints _ _ (T147_53 i) (hfix147_53 i) _)
      ⟨147, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T147_53_2 Q2.hfix147_53_2 Q2.hinj147_53_2
      Q2.hcardT147_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_53_2 i) (Q2.hfix147_53_2 i) _)
      colCert_147_53_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T147_53
      hfix147_53 hinj147_53 hcardT147_53
      (fun i => conj_mem_of_fixedPoints _ _ (T147_53 i) (hfix147_53 i) _)
      ⟨147, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T147_53_2 Q2.hfix147_53_2 Q2.hinj147_53_2
      Q2.hcardT147_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_53_2 i) (Q2.hfix147_53_2 i) _)
      colCert_147_53_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T147_53
      hfix147_53 hinj147_53 hcardT147_53
      (fun i => conj_mem_of_fixedPoints _ _ (T147_53 i) (hfix147_53 i) _)
      ⟨147, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T147_53_2 Q2.hfix147_53_2 Q2.hinj147_53_2
      Q2.hcardT147_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_53_2 i) (Q2.hfix147_53_2 i) _)
      colCert_147_53_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T147_53
      hfix147_53 hinj147_53 hcardT147_53
      (fun i => conj_mem_of_fixedPoints _ _ (T147_53 i) (hfix147_53 i) _)
      ⟨147, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T147_53_2 Q2.hfix147_53_2 Q2.hinj147_53_2
      Q2.hcardT147_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_53_2 i) (Q2.hfix147_53_2 i) _)
      colCert_147_53_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T147_53
      hfix147_53 hinj147_53 hcardT147_53
      (fun i => conj_mem_of_fixedPoints _ _ (T147_53 i) (hfix147_53 i) _)
      ⟨147, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T147_53_2 Q2.hfix147_53_2 Q2.hinj147_53_2
      Q2.hcardT147_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_53_2 i) (Q2.hfix147_53_2 i) _)
      colCert_147_53_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_54_0 (hp : 0 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 0 (transLenTr ⟨54, by decide⟩ 0 hp)) T147_54
      hfix147_54 hinj147_54 hcardT147_54
      (fun i => conj_mem_of_fixedPoints _ _ (T147_54 i) (hfix147_54 i) _)
      ⟨147, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 0 hp) Q2.T147_54_2 Q2.hfix147_54_2 Q2.hinj147_54_2
      Q2.hcardT147_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_54_2 i) (Q2.hfix147_54_2 i) _)
      colCert_147_54_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_54_1 (hp : 1 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 1 (transLenTr ⟨54, by decide⟩ 1 hp)) T147_54
      hfix147_54 hinj147_54 hcardT147_54
      (fun i => conj_mem_of_fixedPoints _ _ (T147_54 i) (hfix147_54 i) _)
      ⟨147, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 1 hp) Q2.T147_54_2 Q2.hfix147_54_2 Q2.hinj147_54_2
      Q2.hcardT147_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_54_2 i) (Q2.hfix147_54_2 i) _)
      colCert_147_54_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_54_2 (hp : 2 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 2 (transLenTr ⟨54, by decide⟩ 2 hp)) T147_54
      hfix147_54 hinj147_54 hcardT147_54
      (fun i => conj_mem_of_fixedPoints _ _ (T147_54 i) (hfix147_54 i) _)
      ⟨147, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 2 hp) Q2.T147_54_2 Q2.hfix147_54_2 Q2.hinj147_54_2
      Q2.hcardT147_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_54_2 i) (Q2.hfix147_54_2 i) _)
      colCert_147_54_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_54_3 (hp : 3 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 3 (transLenTr ⟨54, by decide⟩ 3 hp)) T147_54
      hfix147_54 hinj147_54 hcardT147_54
      (fun i => conj_mem_of_fixedPoints _ _ (T147_54 i) (hfix147_54 i) _)
      ⟨147, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 3 hp) Q2.T147_54_2 Q2.hfix147_54_2 Q2.hinj147_54_2
      Q2.hcardT147_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_54_2 i) (Q2.hfix147_54_2 i) _)
      colCert_147_54_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_54_4 (hp : 4 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 4 (transLenTr ⟨54, by decide⟩ 4 hp)) T147_54
      hfix147_54 hinj147_54 hcardT147_54
      (fun i => conj_mem_of_fixedPoints _ _ (T147_54 i) (hfix147_54 i) _)
      ⟨147, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 4 hp) Q2.T147_54_2 Q2.hfix147_54_2 Q2.hinj147_54_2
      Q2.hcardT147_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_54_2 i) (Q2.hfix147_54_2 i) _)
      colCert_147_54_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_54_5 (hp : 5 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 5 (transLenTr ⟨54, by decide⟩ 5 hp)) T147_54
      hfix147_54 hinj147_54 hcardT147_54
      (fun i => conj_mem_of_fixedPoints _ _ (T147_54 i) (hfix147_54 i) _)
      ⟨147, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 5 hp) Q2.T147_54_2 Q2.hfix147_54_2 Q2.hinj147_54_2
      Q2.hcardT147_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_54_2 i) (Q2.hfix147_54_2 i) _)
      colCert_147_54_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_54_10 (hp : 10 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 10 (transLenTr ⟨54, by decide⟩ 10 hp)) T147_54
      hfix147_54 hinj147_54 hcardT147_54
      (fun i => conj_mem_of_fixedPoints _ _ (T147_54 i) (hfix147_54 i) _)
      ⟨147, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 10 hp) Q2.T147_54_2 Q2.hfix147_54_2 Q2.hinj147_54_2
      Q2.hcardT147_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_54_2 i) (Q2.hfix147_54_2 i) _)
      colCert_147_54_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_54_15 (hp : 15 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 15 (transLenTr ⟨54, by decide⟩ 15 hp)) T147_54
      hfix147_54 hinj147_54 hcardT147_54
      (fun i => conj_mem_of_fixedPoints _ _ (T147_54 i) (hfix147_54 i) _)
      ⟨147, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 15 hp) Q2.T147_54_2 Q2.hfix147_54_2 Q2.hinj147_54_2
      Q2.hcardT147_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_54_2 i) (Q2.hfix147_54_2 i) _)
      colCert_147_54_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_54_20 (hp : 20 < (Q2.transData.getD 54 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨54, by decide⟩ : Fin 148)) (colE2 ⟨54, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨54, by decide⟩ : Fin 148))
        (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨54, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨54, by decide⟩ 20 (transLenTr ⟨54, by decide⟩ 20 hp)) T147_54
      hfix147_54 hinj147_54 hcardT147_54
      (fun i => conj_mem_of_fixedPoints _ _ (T147_54 i) (hfix147_54 i) _)
      ⟨147, by decide⟩ ⟨54, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨54, by decide⟩ 20 hp) Q2.T147_54_2 Q2.hfix147_54_2 Q2.hinj147_54_2
      Q2.hcardT147_54_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_54_2 i) (Q2.hfix147_54_2 i) _)
      colCert_147_54_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_55_0 (hp : 0 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 0 (transLenTr ⟨55, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 0 (transLenTr ⟨55, by decide⟩ 0 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 0 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      colCert_147_55_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_55_1 (hp : 1 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 1 (transLenTr ⟨55, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 1 (transLenTr ⟨55, by decide⟩ 1 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 1 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      colCert_147_55_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_55_2 (hp : 2 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 2 (transLenTr ⟨55, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 2 (transLenTr ⟨55, by decide⟩ 2 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 2 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      colCert_147_55_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_55_3 (hp : 3 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 3 (transLenTr ⟨55, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 3 (transLenTr ⟨55, by decide⟩ 3 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 3 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      colCert_147_55_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_55_4 (hp : 4 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 4 (transLenTr ⟨55, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 4 (transLenTr ⟨55, by decide⟩ 4 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 4 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      colCert_147_55_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_55_5 (hp : 5 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 5 (transLenTr ⟨55, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 5 (transLenTr ⟨55, by decide⟩ 5 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 5 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 5 (transLenTr ⟨55, by decide⟩ 5 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_5.D1 (m := 1) from colCertDiv_147_55_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 5 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_5.D2 (m := 1) from colCertDiv_147_55_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_5_match


theorem leaf_147_55_6 (hp : 6 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 6 (transLenTr ⟨55, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 6 (transLenTr ⟨55, by decide⟩ 6 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 6 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 6 (transLenTr ⟨55, by decide⟩ 6 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_6.D1 (m := 1) from colCertDiv_147_55_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 6 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_6.D2 (m := 1) from colCertDiv_147_55_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_6_match


theorem leaf_147_55_7 (hp : 7 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 7 (transLenTr ⟨55, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 7 (transLenTr ⟨55, by decide⟩ 7 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 7 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 7 (transLenTr ⟨55, by decide⟩ 7 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_7.D1 (m := 1) from colCertDiv_147_55_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 7 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_7.D2 (m := 1) from colCertDiv_147_55_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_7_match


theorem leaf_147_55_8 (hp : 8 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 8 (transLenTr ⟨55, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 8 (transLenTr ⟨55, by decide⟩ 8 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 8 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 8 (transLenTr ⟨55, by decide⟩ 8 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_8.D1 (m := 1) from colCertDiv_147_55_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 8 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_8.D2 (m := 1) from colCertDiv_147_55_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_8_match


theorem leaf_147_55_9 (hp : 9 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 9 (transLenTr ⟨55, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 9 (transLenTr ⟨55, by decide⟩ 9 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 9 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 9 (transLenTr ⟨55, by decide⟩ 9 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_9.D1 (m := 1) from colCertDiv_147_55_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 9 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_9.D2 (m := 1) from colCertDiv_147_55_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_9_match


theorem leaf_147_55_10 (hp : 10 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 10 (transLenTr ⟨55, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 10 (transLenTr ⟨55, by decide⟩ 10 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 10 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 10 (transLenTr ⟨55, by decide⟩ 10 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_10.D1 (m := 1) from colCertDiv_147_55_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 10 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_10.D2 (m := 1) from colCertDiv_147_55_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_10_match


theorem leaf_147_55_11 (hp : 11 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 11 (transLenTr ⟨55, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 11 (transLenTr ⟨55, by decide⟩ 11 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 11 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 11 (transLenTr ⟨55, by decide⟩ 11 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_11.D1 (m := 1) from colCertDiv_147_55_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 11 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_11.D2 (m := 1) from colCertDiv_147_55_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_11_match


theorem leaf_147_55_12 (hp : 12 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 12 (transLenTr ⟨55, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 12 (transLenTr ⟨55, by decide⟩ 12 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 12 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 12 (transLenTr ⟨55, by decide⟩ 12 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_12.D1 (m := 1) from colCertDiv_147_55_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 12 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_12.D2 (m := 1) from colCertDiv_147_55_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_12_match


theorem leaf_147_55_13 (hp : 13 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 13 (transLenTr ⟨55, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 13 (transLenTr ⟨55, by decide⟩ 13 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 13 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 13 (transLenTr ⟨55, by decide⟩ 13 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_13.D1 (m := 1) from colCertDiv_147_55_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 13 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_13.D2 (m := 1) from colCertDiv_147_55_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_13_match


theorem leaf_147_55_14 (hp : 14 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 14 (transLenTr ⟨55, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 14 (transLenTr ⟨55, by decide⟩ 14 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 14 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 14 (transLenTr ⟨55, by decide⟩ 14 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_14.D1 (m := 1) from colCertDiv_147_55_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 14 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_14.D2 (m := 1) from colCertDiv_147_55_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_14_match


theorem leaf_147_55_15 (hp : 15 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 15 (transLenTr ⟨55, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 15 (transLenTr ⟨55, by decide⟩ 15 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 15 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 15 (transLenTr ⟨55, by decide⟩ 15 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_15.D1 (m := 1) from colCertDiv_147_55_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 15 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_15.D2 (m := 1) from colCertDiv_147_55_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_15_match


theorem leaf_147_55_16 (hp : 16 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 16 (transLenTr ⟨55, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 16 (transLenTr ⟨55, by decide⟩ 16 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 16 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 16 (transLenTr ⟨55, by decide⟩ 16 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_16.D1 (m := 1) from colCertDiv_147_55_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 16 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_16.D2 (m := 1) from colCertDiv_147_55_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_16_match


theorem leaf_147_55_17 (hp : 17 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 17 (transLenTr ⟨55, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 17 (transLenTr ⟨55, by decide⟩ 17 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 17 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 17 (transLenTr ⟨55, by decide⟩ 17 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_17.D1 (m := 1) from colCertDiv_147_55_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 17 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_17.D2 (m := 1) from colCertDiv_147_55_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_17_match


theorem leaf_147_55_18 (hp : 18 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 18 (transLenTr ⟨55, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 18 (transLenTr ⟨55, by decide⟩ 18 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 18 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 18 (transLenTr ⟨55, by decide⟩ 18 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_18.D1 (m := 1) from colCertDiv_147_55_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 18 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_18.D2 (m := 1) from colCertDiv_147_55_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_18_match


theorem leaf_147_55_19 (hp : 19 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 19 (transLenTr ⟨55, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 19 (transLenTr ⟨55, by decide⟩ 19 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 19 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 19 (transLenTr ⟨55, by decide⟩ 19 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_19.D1 (m := 1) from colCertDiv_147_55_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 19 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_19.D2 (m := 1) from colCertDiv_147_55_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_19_match


theorem leaf_147_55_20 (hp : 20 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 20 (transLenTr ⟨55, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 20 (transLenTr ⟨55, by decide⟩ 20 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 20 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 20 (transLenTr ⟨55, by decide⟩ 20 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_20.D1 (m := 1) from colCertDiv_147_55_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 20 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_20.D2 (m := 1) from colCertDiv_147_55_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_20_match


theorem leaf_147_55_21 (hp : 21 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 21 (transLenTr ⟨55, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 21 (transLenTr ⟨55, by decide⟩ 21 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 21 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 21 (transLenTr ⟨55, by decide⟩ 21 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_21.D1 (m := 1) from colCertDiv_147_55_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 21 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_21.D2 (m := 1) from colCertDiv_147_55_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_21_match


theorem leaf_147_55_22 (hp : 22 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 22 (transLenTr ⟨55, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 22 (transLenTr ⟨55, by decide⟩ 22 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 22 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 22 (transLenTr ⟨55, by decide⟩ 22 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_22.D1 (m := 1) from colCertDiv_147_55_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 22 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_22.D2 (m := 1) from colCertDiv_147_55_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_22_match


theorem leaf_147_55_23 (hp : 23 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 23 (transLenTr ⟨55, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 23 (transLenTr ⟨55, by decide⟩ 23 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 23 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 23 (transLenTr ⟨55, by decide⟩ 23 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_23.D1 (m := 1) from colCertDiv_147_55_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 23 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_23.D2 (m := 1) from colCertDiv_147_55_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_23_match


theorem leaf_147_55_24 (hp : 24 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 24 (transLenTr ⟨55, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 24 (transLenTr ⟨55, by decide⟩ 24 hp)) T147_55
      hfix147_55 hinj147_55 hcardT147_55
      (fun i => conj_mem_of_fixedPoints _ _ (T147_55 i) (hfix147_55 i) _)
      ⟨147, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 24 hp) Q2.T147_55_2 Q2.hfix147_55_2 Q2.hinj147_55_2
      Q2.hcardT147_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_55_2 i) (Q2.hfix147_55_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨55, by decide⟩ 24 (transLenTr ⟨55, by decide⟩ 24 hp) : ↥(reps ⟨55, by decide⟩)) : Coordinate 1)
        T147_55 = colFn colCertDiv_147_55_24.D1 (m := 1) from colCertDiv_147_55_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨55, by decide⟩ 24 hp : ↥(Q2.reps ⟨55, by decide⟩)) : Coordinate 2)
        Q2.T147_55_2 = colFn colCertDiv_147_55_24.D2 (m := 1) from colCertDiv_147_55_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_55_24_match


theorem leaf_147_56_0 (hp : 0 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 0 (transLenTr ⟨56, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 0 (transLenTr ⟨56, by decide⟩ 0 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 0 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      colCert_147_56_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_56_1 (hp : 1 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 1 (transLenTr ⟨56, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 1 (transLenTr ⟨56, by decide⟩ 1 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 1 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      colCert_147_56_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_56_2 (hp : 2 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 2 (transLenTr ⟨56, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 2 (transLenTr ⟨56, by decide⟩ 2 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 2 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      colCert_147_56_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_56_3 (hp : 3 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 3 (transLenTr ⟨56, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 3 (transLenTr ⟨56, by decide⟩ 3 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 3 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      colCert_147_56_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_56_4 (hp : 4 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 4 (transLenTr ⟨56, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 4 (transLenTr ⟨56, by decide⟩ 4 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 4 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      colCert_147_56_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_56_5 (hp : 5 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 5 (transLenTr ⟨56, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 5 (transLenTr ⟨56, by decide⟩ 5 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 5 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 5 (transLenTr ⟨56, by decide⟩ 5 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_5.D1 (m := 1) from colCertDiv_147_56_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 5 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_5.D2 (m := 1) from colCertDiv_147_56_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_5_match


theorem leaf_147_56_6 (hp : 6 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 6 (transLenTr ⟨56, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 6 (transLenTr ⟨56, by decide⟩ 6 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 6 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 6 (transLenTr ⟨56, by decide⟩ 6 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_6.D1 (m := 1) from colCertDiv_147_56_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 6 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_6.D2 (m := 1) from colCertDiv_147_56_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_6_match


theorem leaf_147_56_7 (hp : 7 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 7 (transLenTr ⟨56, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 7 (transLenTr ⟨56, by decide⟩ 7 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 7 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 7 (transLenTr ⟨56, by decide⟩ 7 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_7.D1 (m := 1) from colCertDiv_147_56_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 7 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_7.D2 (m := 1) from colCertDiv_147_56_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_7_match


theorem leaf_147_56_8 (hp : 8 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 8 (transLenTr ⟨56, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 8 (transLenTr ⟨56, by decide⟩ 8 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 8 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 8 (transLenTr ⟨56, by decide⟩ 8 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_8.D1 (m := 1) from colCertDiv_147_56_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 8 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_8.D2 (m := 1) from colCertDiv_147_56_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_8_match


theorem leaf_147_56_9 (hp : 9 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 9 (transLenTr ⟨56, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 9 (transLenTr ⟨56, by decide⟩ 9 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 9 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 9 (transLenTr ⟨56, by decide⟩ 9 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_9.D1 (m := 1) from colCertDiv_147_56_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 9 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_9.D2 (m := 1) from colCertDiv_147_56_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_9_match


theorem leaf_147_56_10 (hp : 10 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 10 (transLenTr ⟨56, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 10 (transLenTr ⟨56, by decide⟩ 10 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 10 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 10 (transLenTr ⟨56, by decide⟩ 10 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_10.D1 (m := 1) from colCertDiv_147_56_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 10 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_10.D2 (m := 1) from colCertDiv_147_56_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_10_match


theorem leaf_147_56_11 (hp : 11 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 11 (transLenTr ⟨56, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 11 (transLenTr ⟨56, by decide⟩ 11 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 11 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 11 (transLenTr ⟨56, by decide⟩ 11 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_11.D1 (m := 1) from colCertDiv_147_56_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 11 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_11.D2 (m := 1) from colCertDiv_147_56_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_11_match


theorem leaf_147_56_12 (hp : 12 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 12 (transLenTr ⟨56, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 12 (transLenTr ⟨56, by decide⟩ 12 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 12 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 12 (transLenTr ⟨56, by decide⟩ 12 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_12.D1 (m := 1) from colCertDiv_147_56_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 12 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_12.D2 (m := 1) from colCertDiv_147_56_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_12_match


theorem leaf_147_56_13 (hp : 13 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 13 (transLenTr ⟨56, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 13 (transLenTr ⟨56, by decide⟩ 13 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 13 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 13 (transLenTr ⟨56, by decide⟩ 13 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_13.D1 (m := 1) from colCertDiv_147_56_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 13 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_13.D2 (m := 1) from colCertDiv_147_56_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_13_match


theorem leaf_147_56_14 (hp : 14 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 14 (transLenTr ⟨56, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 14 (transLenTr ⟨56, by decide⟩ 14 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 14 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 14 (transLenTr ⟨56, by decide⟩ 14 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_14.D1 (m := 1) from colCertDiv_147_56_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 14 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_14.D2 (m := 1) from colCertDiv_147_56_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_14_match


theorem leaf_147_56_15 (hp : 15 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 15 (transLenTr ⟨56, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 15 (transLenTr ⟨56, by decide⟩ 15 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 15 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 15 (transLenTr ⟨56, by decide⟩ 15 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_15.D1 (m := 1) from colCertDiv_147_56_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 15 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_15.D2 (m := 1) from colCertDiv_147_56_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_15_match


theorem leaf_147_56_16 (hp : 16 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 16 (transLenTr ⟨56, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 16 (transLenTr ⟨56, by decide⟩ 16 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 16 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 16 (transLenTr ⟨56, by decide⟩ 16 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_16.D1 (m := 1) from colCertDiv_147_56_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 16 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_16.D2 (m := 1) from colCertDiv_147_56_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_16_match


theorem leaf_147_56_17 (hp : 17 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 17 (transLenTr ⟨56, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 17 (transLenTr ⟨56, by decide⟩ 17 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 17 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 17 (transLenTr ⟨56, by decide⟩ 17 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_17.D1 (m := 1) from colCertDiv_147_56_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 17 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_17.D2 (m := 1) from colCertDiv_147_56_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_17_match


theorem leaf_147_56_18 (hp : 18 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 18 (transLenTr ⟨56, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 18 (transLenTr ⟨56, by decide⟩ 18 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 18 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 18 (transLenTr ⟨56, by decide⟩ 18 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_18.D1 (m := 1) from colCertDiv_147_56_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 18 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_18.D2 (m := 1) from colCertDiv_147_56_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_18_match


theorem leaf_147_56_19 (hp : 19 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 19 (transLenTr ⟨56, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 19 (transLenTr ⟨56, by decide⟩ 19 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 19 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 19 (transLenTr ⟨56, by decide⟩ 19 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_19.D1 (m := 1) from colCertDiv_147_56_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 19 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_19.D2 (m := 1) from colCertDiv_147_56_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_19_match


theorem leaf_147_56_20 (hp : 20 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 20 (transLenTr ⟨56, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 20 (transLenTr ⟨56, by decide⟩ 20 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 20 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 20 (transLenTr ⟨56, by decide⟩ 20 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_20.D1 (m := 1) from colCertDiv_147_56_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 20 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_20.D2 (m := 1) from colCertDiv_147_56_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_20_match


theorem leaf_147_56_21 (hp : 21 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 21 (transLenTr ⟨56, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 21 (transLenTr ⟨56, by decide⟩ 21 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 21 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 21 (transLenTr ⟨56, by decide⟩ 21 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_21.D1 (m := 1) from colCertDiv_147_56_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 21 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_21.D2 (m := 1) from colCertDiv_147_56_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_21_match


theorem leaf_147_56_22 (hp : 22 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 22 (transLenTr ⟨56, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 22 (transLenTr ⟨56, by decide⟩ 22 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 22 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 22 (transLenTr ⟨56, by decide⟩ 22 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_22.D1 (m := 1) from colCertDiv_147_56_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 22 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_22.D2 (m := 1) from colCertDiv_147_56_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_22_match


theorem leaf_147_56_23 (hp : 23 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 23 (transLenTr ⟨56, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 23 (transLenTr ⟨56, by decide⟩ 23 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 23 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 23 (transLenTr ⟨56, by decide⟩ 23 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_23.D1 (m := 1) from colCertDiv_147_56_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 23 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_23.D2 (m := 1) from colCertDiv_147_56_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_23_match


theorem leaf_147_56_24 (hp : 24 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 24 (transLenTr ⟨56, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 24 (transLenTr ⟨56, by decide⟩ 24 hp)) T147_56
      hfix147_56 hinj147_56 hcardT147_56
      (fun i => conj_mem_of_fixedPoints _ _ (T147_56 i) (hfix147_56 i) _)
      ⟨147, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 24 hp) Q2.T147_56_2 Q2.hfix147_56_2 Q2.hinj147_56_2
      Q2.hcardT147_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_56_2 i) (Q2.hfix147_56_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨56, by decide⟩ 24 (transLenTr ⟨56, by decide⟩ 24 hp) : ↥(reps ⟨56, by decide⟩)) : Coordinate 1)
        T147_56 = colFn colCertDiv_147_56_24.D1 (m := 1) from colCertDiv_147_56_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨56, by decide⟩ 24 hp : ↥(Q2.reps ⟨56, by decide⟩)) : Coordinate 2)
        Q2.T147_56_2 = colFn colCertDiv_147_56_24.D2 (m := 1) from colCertDiv_147_56_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_56_24_match


theorem leaf_147_57_0 (hp : 0 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 0 (transLenTr ⟨57, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 0 (transLenTr ⟨57, by decide⟩ 0 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 0 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      colCert_147_57_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_57_1 (hp : 1 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 1 (transLenTr ⟨57, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 1 (transLenTr ⟨57, by decide⟩ 1 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 1 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      colCert_147_57_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_57_2 (hp : 2 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 2 (transLenTr ⟨57, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 2 (transLenTr ⟨57, by decide⟩ 2 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 2 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      colCert_147_57_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_57_3 (hp : 3 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 3 (transLenTr ⟨57, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 3 (transLenTr ⟨57, by decide⟩ 3 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 3 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      colCert_147_57_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_57_4 (hp : 4 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 4 (transLenTr ⟨57, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 4 (transLenTr ⟨57, by decide⟩ 4 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 4 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      colCert_147_57_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_57_5 (hp : 5 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 5 (transLenTr ⟨57, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 5 (transLenTr ⟨57, by decide⟩ 5 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 5 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 5 (transLenTr ⟨57, by decide⟩ 5 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_5.D1 (m := 1) from colCertDiv_147_57_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 5 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_5.D2 (m := 1) from colCertDiv_147_57_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_5_match


theorem leaf_147_57_6 (hp : 6 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 6 (transLenTr ⟨57, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 6 (transLenTr ⟨57, by decide⟩ 6 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 6 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 6 (transLenTr ⟨57, by decide⟩ 6 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_6.D1 (m := 1) from colCertDiv_147_57_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 6 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_6.D2 (m := 1) from colCertDiv_147_57_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_6_match


theorem leaf_147_57_7 (hp : 7 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 7 (transLenTr ⟨57, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 7 (transLenTr ⟨57, by decide⟩ 7 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 7 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 7 (transLenTr ⟨57, by decide⟩ 7 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_7.D1 (m := 1) from colCertDiv_147_57_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 7 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_7.D2 (m := 1) from colCertDiv_147_57_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_7_match


theorem leaf_147_57_8 (hp : 8 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 8 (transLenTr ⟨57, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 8 (transLenTr ⟨57, by decide⟩ 8 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 8 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 8 (transLenTr ⟨57, by decide⟩ 8 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_8.D1 (m := 1) from colCertDiv_147_57_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 8 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_8.D2 (m := 1) from colCertDiv_147_57_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_8_match


theorem leaf_147_57_9 (hp : 9 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 9 (transLenTr ⟨57, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 9 (transLenTr ⟨57, by decide⟩ 9 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 9 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 9 (transLenTr ⟨57, by decide⟩ 9 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_9.D1 (m := 1) from colCertDiv_147_57_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 9 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_9.D2 (m := 1) from colCertDiv_147_57_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_9_match


theorem leaf_147_57_10 (hp : 10 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 10 (transLenTr ⟨57, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 10 (transLenTr ⟨57, by decide⟩ 10 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 10 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 10 (transLenTr ⟨57, by decide⟩ 10 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_10.D1 (m := 1) from colCertDiv_147_57_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 10 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_10.D2 (m := 1) from colCertDiv_147_57_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_10_match


theorem leaf_147_57_11 (hp : 11 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 11 (transLenTr ⟨57, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 11 (transLenTr ⟨57, by decide⟩ 11 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 11 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 11 (transLenTr ⟨57, by decide⟩ 11 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_11.D1 (m := 1) from colCertDiv_147_57_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 11 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_11.D2 (m := 1) from colCertDiv_147_57_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_11_match


theorem leaf_147_57_12 (hp : 12 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 12 (transLenTr ⟨57, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 12 (transLenTr ⟨57, by decide⟩ 12 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 12 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 12 (transLenTr ⟨57, by decide⟩ 12 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_12.D1 (m := 1) from colCertDiv_147_57_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 12 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_12.D2 (m := 1) from colCertDiv_147_57_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_12_match


theorem leaf_147_57_13 (hp : 13 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 13 (transLenTr ⟨57, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 13 (transLenTr ⟨57, by decide⟩ 13 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 13 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 13 (transLenTr ⟨57, by decide⟩ 13 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_13.D1 (m := 1) from colCertDiv_147_57_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 13 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_13.D2 (m := 1) from colCertDiv_147_57_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_13_match


theorem leaf_147_57_14 (hp : 14 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 14 (transLenTr ⟨57, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 14 (transLenTr ⟨57, by decide⟩ 14 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 14 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 14 (transLenTr ⟨57, by decide⟩ 14 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_14.D1 (m := 1) from colCertDiv_147_57_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 14 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_14.D2 (m := 1) from colCertDiv_147_57_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_14_match


theorem leaf_147_57_15 (hp : 15 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 15 (transLenTr ⟨57, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 15 (transLenTr ⟨57, by decide⟩ 15 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 15 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 15 (transLenTr ⟨57, by decide⟩ 15 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_15.D1 (m := 1) from colCertDiv_147_57_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 15 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_15.D2 (m := 1) from colCertDiv_147_57_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_15_match


theorem leaf_147_57_16 (hp : 16 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 16 (transLenTr ⟨57, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 16 (transLenTr ⟨57, by decide⟩ 16 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 16 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 16 (transLenTr ⟨57, by decide⟩ 16 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_16.D1 (m := 1) from colCertDiv_147_57_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 16 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_16.D2 (m := 1) from colCertDiv_147_57_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_16_match


theorem leaf_147_57_17 (hp : 17 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 17 (transLenTr ⟨57, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 17 (transLenTr ⟨57, by decide⟩ 17 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 17 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 17 (transLenTr ⟨57, by decide⟩ 17 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_17.D1 (m := 1) from colCertDiv_147_57_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 17 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_17.D2 (m := 1) from colCertDiv_147_57_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_17_match


theorem leaf_147_57_18 (hp : 18 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 18 (transLenTr ⟨57, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 18 (transLenTr ⟨57, by decide⟩ 18 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 18 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 18 (transLenTr ⟨57, by decide⟩ 18 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_18.D1 (m := 1) from colCertDiv_147_57_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 18 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_18.D2 (m := 1) from colCertDiv_147_57_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_18_match


theorem leaf_147_57_19 (hp : 19 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 19 (transLenTr ⟨57, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 19 (transLenTr ⟨57, by decide⟩ 19 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 19 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 19 (transLenTr ⟨57, by decide⟩ 19 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_19.D1 (m := 1) from colCertDiv_147_57_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 19 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_19.D2 (m := 1) from colCertDiv_147_57_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_19_match


theorem leaf_147_57_20 (hp : 20 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 20 (transLenTr ⟨57, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 20 (transLenTr ⟨57, by decide⟩ 20 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 20 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 20 (transLenTr ⟨57, by decide⟩ 20 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_20.D1 (m := 1) from colCertDiv_147_57_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 20 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_20.D2 (m := 1) from colCertDiv_147_57_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_20_match


theorem leaf_147_57_21 (hp : 21 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 21 (transLenTr ⟨57, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 21 (transLenTr ⟨57, by decide⟩ 21 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 21 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 21 (transLenTr ⟨57, by decide⟩ 21 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_21.D1 (m := 1) from colCertDiv_147_57_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 21 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_21.D2 (m := 1) from colCertDiv_147_57_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_21_match


theorem leaf_147_57_22 (hp : 22 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 22 (transLenTr ⟨57, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 22 (transLenTr ⟨57, by decide⟩ 22 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 22 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 22 (transLenTr ⟨57, by decide⟩ 22 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_22.D1 (m := 1) from colCertDiv_147_57_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 22 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_22.D2 (m := 1) from colCertDiv_147_57_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_22_match


theorem leaf_147_57_23 (hp : 23 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 23 (transLenTr ⟨57, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 23 (transLenTr ⟨57, by decide⟩ 23 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 23 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 23 (transLenTr ⟨57, by decide⟩ 23 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_23.D1 (m := 1) from colCertDiv_147_57_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 23 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_23.D2 (m := 1) from colCertDiv_147_57_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_23_match


theorem leaf_147_57_24 (hp : 24 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 24 (transLenTr ⟨57, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 24 (transLenTr ⟨57, by decide⟩ 24 hp)) T147_57
      hfix147_57 hinj147_57 hcardT147_57
      (fun i => conj_mem_of_fixedPoints _ _ (T147_57 i) (hfix147_57 i) _)
      ⟨147, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 24 hp) Q2.T147_57_2 Q2.hfix147_57_2 Q2.hinj147_57_2
      Q2.hcardT147_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_57_2 i) (Q2.hfix147_57_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨57, by decide⟩ 24 (transLenTr ⟨57, by decide⟩ 24 hp) : ↥(reps ⟨57, by decide⟩)) : Coordinate 1)
        T147_57 = colFn colCertDiv_147_57_24.D1 (m := 1) from colCertDiv_147_57_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨57, by decide⟩ 24 hp : ↥(Q2.reps ⟨57, by decide⟩)) : Coordinate 2)
        Q2.T147_57_2 = colFn colCertDiv_147_57_24.D2 (m := 1) from colCertDiv_147_57_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_57_24_match


theorem leaf_147_58_0 (hp : 0 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 0 (transLenTr ⟨58, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 0 (transLenTr ⟨58, by decide⟩ 0 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 0 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      colCert_147_58_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_58_1 (hp : 1 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 1 (transLenTr ⟨58, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 1 (transLenTr ⟨58, by decide⟩ 1 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 1 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      colCert_147_58_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_58_2 (hp : 2 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 2 (transLenTr ⟨58, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 2 (transLenTr ⟨58, by decide⟩ 2 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 2 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      colCert_147_58_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_58_3 (hp : 3 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 3 (transLenTr ⟨58, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 3 (transLenTr ⟨58, by decide⟩ 3 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 3 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      colCert_147_58_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_58_4 (hp : 4 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 4 (transLenTr ⟨58, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 4 (transLenTr ⟨58, by decide⟩ 4 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 4 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      colCert_147_58_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_58_5 (hp : 5 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 5 (transLenTr ⟨58, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 5 (transLenTr ⟨58, by decide⟩ 5 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 5 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 5 (transLenTr ⟨58, by decide⟩ 5 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_5.D1 (m := 1) from colCertDiv_147_58_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 5 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_5.D2 (m := 1) from colCertDiv_147_58_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_5_match


theorem leaf_147_58_6 (hp : 6 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 6 (transLenTr ⟨58, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 6 (transLenTr ⟨58, by decide⟩ 6 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 6 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 6 (transLenTr ⟨58, by decide⟩ 6 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_6.D1 (m := 1) from colCertDiv_147_58_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 6 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_6.D2 (m := 1) from colCertDiv_147_58_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_6_match


theorem leaf_147_58_7 (hp : 7 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 7 (transLenTr ⟨58, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 7 (transLenTr ⟨58, by decide⟩ 7 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 7 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 7 (transLenTr ⟨58, by decide⟩ 7 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_7.D1 (m := 1) from colCertDiv_147_58_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 7 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_7.D2 (m := 1) from colCertDiv_147_58_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_7_match


theorem leaf_147_58_8 (hp : 8 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 8 (transLenTr ⟨58, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 8 (transLenTr ⟨58, by decide⟩ 8 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 8 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 8 (transLenTr ⟨58, by decide⟩ 8 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_8.D1 (m := 1) from colCertDiv_147_58_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 8 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_8.D2 (m := 1) from colCertDiv_147_58_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_8_match


theorem leaf_147_58_9 (hp : 9 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 9 (transLenTr ⟨58, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 9 (transLenTr ⟨58, by decide⟩ 9 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 9 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 9 (transLenTr ⟨58, by decide⟩ 9 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_9.D1 (m := 1) from colCertDiv_147_58_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 9 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_9.D2 (m := 1) from colCertDiv_147_58_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_9_match


theorem leaf_147_58_10 (hp : 10 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 10 (transLenTr ⟨58, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 10 (transLenTr ⟨58, by decide⟩ 10 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 10 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 10 (transLenTr ⟨58, by decide⟩ 10 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_10.D1 (m := 1) from colCertDiv_147_58_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 10 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_10.D2 (m := 1) from colCertDiv_147_58_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_10_match


theorem leaf_147_58_11 (hp : 11 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 11 (transLenTr ⟨58, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 11 (transLenTr ⟨58, by decide⟩ 11 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 11 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 11 (transLenTr ⟨58, by decide⟩ 11 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_11.D1 (m := 1) from colCertDiv_147_58_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 11 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_11.D2 (m := 1) from colCertDiv_147_58_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_11_match


theorem leaf_147_58_12 (hp : 12 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 12 (transLenTr ⟨58, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 12 (transLenTr ⟨58, by decide⟩ 12 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 12 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 12 (transLenTr ⟨58, by decide⟩ 12 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_12.D1 (m := 1) from colCertDiv_147_58_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 12 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_12.D2 (m := 1) from colCertDiv_147_58_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_12_match


theorem leaf_147_58_13 (hp : 13 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 13 (transLenTr ⟨58, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 13 (transLenTr ⟨58, by decide⟩ 13 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 13 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 13 (transLenTr ⟨58, by decide⟩ 13 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_13.D1 (m := 1) from colCertDiv_147_58_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 13 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_13.D2 (m := 1) from colCertDiv_147_58_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_13_match


theorem leaf_147_58_14 (hp : 14 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 14 (transLenTr ⟨58, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 14 (transLenTr ⟨58, by decide⟩ 14 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 14 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 14 (transLenTr ⟨58, by decide⟩ 14 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_14.D1 (m := 1) from colCertDiv_147_58_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 14 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_14.D2 (m := 1) from colCertDiv_147_58_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_14_match


theorem leaf_147_58_15 (hp : 15 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 15 (transLenTr ⟨58, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 15 (transLenTr ⟨58, by decide⟩ 15 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 15 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 15 (transLenTr ⟨58, by decide⟩ 15 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_15.D1 (m := 1) from colCertDiv_147_58_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 15 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_15.D2 (m := 1) from colCertDiv_147_58_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_15_match


theorem leaf_147_58_16 (hp : 16 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 16 (transLenTr ⟨58, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 16 (transLenTr ⟨58, by decide⟩ 16 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 16 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 16 (transLenTr ⟨58, by decide⟩ 16 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_16.D1 (m := 1) from colCertDiv_147_58_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 16 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_16.D2 (m := 1) from colCertDiv_147_58_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_16_match


theorem leaf_147_58_17 (hp : 17 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 17 (transLenTr ⟨58, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 17 (transLenTr ⟨58, by decide⟩ 17 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 17 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 17 (transLenTr ⟨58, by decide⟩ 17 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_17.D1 (m := 1) from colCertDiv_147_58_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 17 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_17.D2 (m := 1) from colCertDiv_147_58_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_17_match


theorem leaf_147_58_18 (hp : 18 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 18 (transLenTr ⟨58, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 18 (transLenTr ⟨58, by decide⟩ 18 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 18 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 18 (transLenTr ⟨58, by decide⟩ 18 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_18.D1 (m := 1) from colCertDiv_147_58_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 18 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_18.D2 (m := 1) from colCertDiv_147_58_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_18_match


theorem leaf_147_58_19 (hp : 19 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 19 (transLenTr ⟨58, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 19 (transLenTr ⟨58, by decide⟩ 19 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 19 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 19 (transLenTr ⟨58, by decide⟩ 19 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_19.D1 (m := 1) from colCertDiv_147_58_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 19 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_19.D2 (m := 1) from colCertDiv_147_58_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_19_match


theorem leaf_147_58_20 (hp : 20 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 20 (transLenTr ⟨58, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 20 (transLenTr ⟨58, by decide⟩ 20 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 20 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 20 (transLenTr ⟨58, by decide⟩ 20 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_20.D1 (m := 1) from colCertDiv_147_58_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 20 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_20.D2 (m := 1) from colCertDiv_147_58_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_20_match


theorem leaf_147_58_21 (hp : 21 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 21 (transLenTr ⟨58, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 21 (transLenTr ⟨58, by decide⟩ 21 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 21 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 21 (transLenTr ⟨58, by decide⟩ 21 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_21.D1 (m := 1) from colCertDiv_147_58_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 21 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_21.D2 (m := 1) from colCertDiv_147_58_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_21_match


theorem leaf_147_58_22 (hp : 22 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 22 (transLenTr ⟨58, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 22 (transLenTr ⟨58, by decide⟩ 22 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 22 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 22 (transLenTr ⟨58, by decide⟩ 22 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_22.D1 (m := 1) from colCertDiv_147_58_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 22 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_22.D2 (m := 1) from colCertDiv_147_58_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_22_match


theorem leaf_147_58_23 (hp : 23 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 23 (transLenTr ⟨58, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 23 (transLenTr ⟨58, by decide⟩ 23 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 23 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 23 (transLenTr ⟨58, by decide⟩ 23 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_23.D1 (m := 1) from colCertDiv_147_58_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 23 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_23.D2 (m := 1) from colCertDiv_147_58_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_23_match


theorem leaf_147_58_24 (hp : 24 < (Q2.transData.getD 58 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨58, by decide⟩ : Fin 148)) (colE2 ⟨58, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨58, by decide⟩ : Fin 148))
        (colE1 ⟨58, by decide⟩ 24 (transLenTr ⟨58, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨58, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨58, by decide⟩ 24 (transLenTr ⟨58, by decide⟩ 24 hp)) T147_58
      hfix147_58 hinj147_58 hcardT147_58
      (fun i => conj_mem_of_fixedPoints _ _ (T147_58 i) (hfix147_58 i) _)
      ⟨147, by decide⟩ ⟨58, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨58, by decide⟩ 24 hp) Q2.T147_58_2 Q2.hfix147_58_2 Q2.hinj147_58_2
      Q2.hcardT147_58_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_58_2 i) (Q2.hfix147_58_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨58, by decide⟩ 24 (transLenTr ⟨58, by decide⟩ 24 hp) : ↥(reps ⟨58, by decide⟩)) : Coordinate 1)
        T147_58 = colFn colCertDiv_147_58_24.D1 (m := 1) from colCertDiv_147_58_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨58, by decide⟩ 24 hp : ↥(Q2.reps ⟨58, by decide⟩)) : Coordinate 2)
        Q2.T147_58_2 = colFn colCertDiv_147_58_24.D2 (m := 1) from colCertDiv_147_58_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_58_24_match


theorem leaf_147_59_0 (hp : 0 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 0 (transLenTr ⟨59, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 0 (transLenTr ⟨59, by decide⟩ 0 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 0 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_1 (hp : 1 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 1 (transLenTr ⟨59, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 1 (transLenTr ⟨59, by decide⟩ 1 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 1 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_2 (hp : 2 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 2 (transLenTr ⟨59, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 2 (transLenTr ⟨59, by decide⟩ 2 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 2 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_3 (hp : 3 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 3 (transLenTr ⟨59, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 3 (transLenTr ⟨59, by decide⟩ 3 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 3 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_4 (hp : 4 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 4 (transLenTr ⟨59, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 4 (transLenTr ⟨59, by decide⟩ 4 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 4 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_5 (hp : 5 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 5 (transLenTr ⟨59, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 5 (transLenTr ⟨59, by decide⟩ 5 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 5 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_6 (hp : 6 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 6 (transLenTr ⟨59, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 6 (transLenTr ⟨59, by decide⟩ 6 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 6 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_7 (hp : 7 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 7 (transLenTr ⟨59, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 7 (transLenTr ⟨59, by decide⟩ 7 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 7 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_8 (hp : 8 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 8 (transLenTr ⟨59, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 8 (transLenTr ⟨59, by decide⟩ 8 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 8 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_9 (hp : 9 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 9 (transLenTr ⟨59, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 9 (transLenTr ⟨59, by decide⟩ 9 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 9 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_10 (hp : 10 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 10 (transLenTr ⟨59, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 10 (transLenTr ⟨59, by decide⟩ 10 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 10 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_10.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_11 (hp : 11 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 11 (transLenTr ⟨59, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 11 (transLenTr ⟨59, by decide⟩ 11 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 11 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_11.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_12 (hp : 12 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 12 (transLenTr ⟨59, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 12 (transLenTr ⟨59, by decide⟩ 12 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 12 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_12.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_13 (hp : 13 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 13 (transLenTr ⟨59, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 13 (transLenTr ⟨59, by decide⟩ 13 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 13 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_13.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_14 (hp : 14 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 14 (transLenTr ⟨59, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 14 (transLenTr ⟨59, by decide⟩ 14 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 14 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_14.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_15 (hp : 15 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 15 (transLenTr ⟨59, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 15 (transLenTr ⟨59, by decide⟩ 15 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 15 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_16 (hp : 16 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 16 (transLenTr ⟨59, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 16 (transLenTr ⟨59, by decide⟩ 16 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 16 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_17 (hp : 17 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 17 (transLenTr ⟨59, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 17 (transLenTr ⟨59, by decide⟩ 17 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 17 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_18 (hp : 18 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 18 (transLenTr ⟨59, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 18 (transLenTr ⟨59, by decide⟩ 18 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 18 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_19 (hp : 19 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 19 (transLenTr ⟨59, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 19 (transLenTr ⟨59, by decide⟩ 19 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 19 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_20 (hp : 20 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 20 (transLenTr ⟨59, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 20 (transLenTr ⟨59, by decide⟩ 20 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 20 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_20.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_21 (hp : 21 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 21 (transLenTr ⟨59, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 21 (transLenTr ⟨59, by decide⟩ 21 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 21 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_21.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_22 (hp : 22 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 22 (transLenTr ⟨59, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 22 (transLenTr ⟨59, by decide⟩ 22 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 22 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_22.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_23 (hp : 23 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 23 (transLenTr ⟨59, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 23 (transLenTr ⟨59, by decide⟩ 23 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 23 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_23.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_59_24 (hp : 24 < (Q2.transData.getD 59 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨59, by decide⟩ : Fin 148)) (colE2 ⟨59, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨59, by decide⟩ : Fin 148))
        (colE1 ⟨59, by decide⟩ 24 (transLenTr ⟨59, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨59, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨59, by decide⟩ 24 (transLenTr ⟨59, by decide⟩ 24 hp)) T147_59
      hfix147_59 hinj147_59 hcardT147_59
      (fun i => conj_mem_of_fixedPoints _ _ (T147_59 i) (hfix147_59 i) _)
      ⟨147, by decide⟩ ⟨59, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨59, by decide⟩ 24 hp) Q2.T147_59_2 Q2.hfix147_59_2 Q2.hinj147_59_2
      Q2.hcardT147_59_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_59_2 i) (Q2.hfix147_59_2 i) _)
      colCert_147_59_24.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_0 (hp : 0 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 0 (transLenTr ⟨60, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 0 (transLenTr ⟨60, by decide⟩ 0 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 0 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      colCert_147_60_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_1 (hp : 1 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 1 (transLenTr ⟨60, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 1 (transLenTr ⟨60, by decide⟩ 1 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 1 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      colCert_147_60_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_2 (hp : 2 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 2 (transLenTr ⟨60, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 2 (transLenTr ⟨60, by decide⟩ 2 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 2 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      colCert_147_60_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_3 (hp : 3 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 3 (transLenTr ⟨60, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 3 (transLenTr ⟨60, by decide⟩ 3 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 3 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      colCert_147_60_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_4 (hp : 4 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 4 (transLenTr ⟨60, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 4 (transLenTr ⟨60, by decide⟩ 4 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 4 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      colCert_147_60_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_5 (hp : 5 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 5 (transLenTr ⟨60, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 5 (transLenTr ⟨60, by decide⟩ 5 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 5 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      colCert_147_60_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_6 (hp : 6 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 6 (transLenTr ⟨60, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 6 (transLenTr ⟨60, by decide⟩ 6 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 6 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      colCert_147_60_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_7 (hp : 7 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 7 (transLenTr ⟨60, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 7 (transLenTr ⟨60, by decide⟩ 7 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 7 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      colCert_147_60_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_8 (hp : 8 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 8 (transLenTr ⟨60, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 8 (transLenTr ⟨60, by decide⟩ 8 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 8 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      colCert_147_60_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_9 (hp : 9 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 9 (transLenTr ⟨60, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 9 (transLenTr ⟨60, by decide⟩ 9 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 9 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      colCert_147_60_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_60_10 (hp : 10 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 10 (transLenTr ⟨60, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 10 (transLenTr ⟨60, by decide⟩ 10 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 10 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 10 (transLenTr ⟨60, by decide⟩ 10 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_10.D1 (m := 1) from colCertDiv_147_60_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 10 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_10.D2 (m := 1) from colCertDiv_147_60_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_10_match


theorem leaf_147_60_11 (hp : 11 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 11 (transLenTr ⟨60, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 11 (transLenTr ⟨60, by decide⟩ 11 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 11 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 11 (transLenTr ⟨60, by decide⟩ 11 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_11.D1 (m := 1) from colCertDiv_147_60_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 11 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_11.D2 (m := 1) from colCertDiv_147_60_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_11_match


theorem leaf_147_60_12 (hp : 12 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 12 (transLenTr ⟨60, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 12 (transLenTr ⟨60, by decide⟩ 12 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 12 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 12 (transLenTr ⟨60, by decide⟩ 12 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_12.D1 (m := 1) from colCertDiv_147_60_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 12 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_12.D2 (m := 1) from colCertDiv_147_60_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_12_match


theorem leaf_147_60_13 (hp : 13 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 13 (transLenTr ⟨60, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 13 (transLenTr ⟨60, by decide⟩ 13 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 13 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 13 (transLenTr ⟨60, by decide⟩ 13 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_13.D1 (m := 1) from colCertDiv_147_60_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 13 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_13.D2 (m := 1) from colCertDiv_147_60_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_13_match


theorem leaf_147_60_14 (hp : 14 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 14 (transLenTr ⟨60, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 14 (transLenTr ⟨60, by decide⟩ 14 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 14 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 14 (transLenTr ⟨60, by decide⟩ 14 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_14.D1 (m := 1) from colCertDiv_147_60_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 14 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_14.D2 (m := 1) from colCertDiv_147_60_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_14_match


theorem leaf_147_60_15 (hp : 15 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 15 (transLenTr ⟨60, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 15 (transLenTr ⟨60, by decide⟩ 15 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 15 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 15 (transLenTr ⟨60, by decide⟩ 15 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_15.D1 (m := 1) from colCertDiv_147_60_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 15 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_15.D2 (m := 1) from colCertDiv_147_60_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_15_match


theorem leaf_147_60_16 (hp : 16 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 16 (transLenTr ⟨60, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 16 (transLenTr ⟨60, by decide⟩ 16 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 16 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 16 (transLenTr ⟨60, by decide⟩ 16 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_16.D1 (m := 1) from colCertDiv_147_60_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 16 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_16.D2 (m := 1) from colCertDiv_147_60_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_16_match


theorem leaf_147_60_17 (hp : 17 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 17 (transLenTr ⟨60, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 17 (transLenTr ⟨60, by decide⟩ 17 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 17 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 17 (transLenTr ⟨60, by decide⟩ 17 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_17.D1 (m := 1) from colCertDiv_147_60_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 17 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_17.D2 (m := 1) from colCertDiv_147_60_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_17_match


theorem leaf_147_60_18 (hp : 18 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 18 (transLenTr ⟨60, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 18 (transLenTr ⟨60, by decide⟩ 18 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 18 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 18 (transLenTr ⟨60, by decide⟩ 18 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_18.D1 (m := 1) from colCertDiv_147_60_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 18 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_18.D2 (m := 1) from colCertDiv_147_60_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_18_match


theorem leaf_147_60_19 (hp : 19 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 19 (transLenTr ⟨60, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 19 (transLenTr ⟨60, by decide⟩ 19 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 19 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 19 (transLenTr ⟨60, by decide⟩ 19 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_19.D1 (m := 1) from colCertDiv_147_60_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 19 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_19.D2 (m := 1) from colCertDiv_147_60_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_19_match


theorem leaf_147_60_20 (hp : 20 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 20 (transLenTr ⟨60, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 20 (transLenTr ⟨60, by decide⟩ 20 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 20 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 20 (transLenTr ⟨60, by decide⟩ 20 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_20.D1 (m := 1) from colCertDiv_147_60_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 20 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_20.D2 (m := 1) from colCertDiv_147_60_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_20_match


theorem leaf_147_60_21 (hp : 21 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 21 (transLenTr ⟨60, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 21 (transLenTr ⟨60, by decide⟩ 21 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 21 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 21 (transLenTr ⟨60, by decide⟩ 21 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_21.D1 (m := 1) from colCertDiv_147_60_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 21 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_21.D2 (m := 1) from colCertDiv_147_60_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_21_match


theorem leaf_147_60_22 (hp : 22 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 22 (transLenTr ⟨60, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 22 (transLenTr ⟨60, by decide⟩ 22 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 22 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 22 (transLenTr ⟨60, by decide⟩ 22 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_22.D1 (m := 1) from colCertDiv_147_60_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 22 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_22.D2 (m := 1) from colCertDiv_147_60_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_22_match


theorem leaf_147_60_23 (hp : 23 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 23 (transLenTr ⟨60, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 23 (transLenTr ⟨60, by decide⟩ 23 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 23 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 23 (transLenTr ⟨60, by decide⟩ 23 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_23.D1 (m := 1) from colCertDiv_147_60_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 23 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_23.D2 (m := 1) from colCertDiv_147_60_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_23_match


theorem leaf_147_60_24 (hp : 24 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 24 (transLenTr ⟨60, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 24 (transLenTr ⟨60, by decide⟩ 24 hp)) T147_60
      hfix147_60 hinj147_60 hcardT147_60
      (fun i => conj_mem_of_fixedPoints _ _ (T147_60 i) (hfix147_60 i) _)
      ⟨147, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 24 hp) Q2.T147_60_2 Q2.hfix147_60_2 Q2.hinj147_60_2
      Q2.hcardT147_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_60_2 i) (Q2.hfix147_60_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨60, by decide⟩ 24 (transLenTr ⟨60, by decide⟩ 24 hp) : ↥(reps ⟨60, by decide⟩)) : Coordinate 1)
        T147_60 = colFn colCertDiv_147_60_24.D1 (m := 1) from colCertDiv_147_60_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨60, by decide⟩ 24 hp : ↥(Q2.reps ⟨60, by decide⟩)) : Coordinate 2)
        Q2.T147_60_2 = colFn colCertDiv_147_60_24.D2 (m := 1) from colCertDiv_147_60_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_60_24_match


theorem leaf_147_61_0 (hp : 0 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 0 (transLenTr ⟨61, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 0 (transLenTr ⟨61, by decide⟩ 0 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 0 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      colCert_147_61_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_61_1 (hp : 1 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 1 (transLenTr ⟨61, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 1 (transLenTr ⟨61, by decide⟩ 1 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 1 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      colCert_147_61_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_61_2 (hp : 2 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 2 (transLenTr ⟨61, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 2 (transLenTr ⟨61, by decide⟩ 2 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 2 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      colCert_147_61_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_61_3 (hp : 3 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 3 (transLenTr ⟨61, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 3 (transLenTr ⟨61, by decide⟩ 3 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 3 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      colCert_147_61_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_61_4 (hp : 4 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 4 (transLenTr ⟨61, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 4 (transLenTr ⟨61, by decide⟩ 4 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 4 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      colCert_147_61_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_61_5 (hp : 5 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 5 (transLenTr ⟨61, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 5 (transLenTr ⟨61, by decide⟩ 5 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 5 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      colCert_147_61_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_61_6 (hp : 6 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 6 (transLenTr ⟨61, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 6 (transLenTr ⟨61, by decide⟩ 6 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 6 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      colCert_147_61_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_61_7 (hp : 7 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 7 (transLenTr ⟨61, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 7 (transLenTr ⟨61, by decide⟩ 7 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 7 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      colCert_147_61_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_61_8 (hp : 8 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 8 (transLenTr ⟨61, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 8 (transLenTr ⟨61, by decide⟩ 8 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 8 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      colCert_147_61_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_61_9 (hp : 9 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 9 (transLenTr ⟨61, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 9 (transLenTr ⟨61, by decide⟩ 9 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 9 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      colCert_147_61_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_61_10 (hp : 10 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 10 (transLenTr ⟨61, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 10 (transLenTr ⟨61, by decide⟩ 10 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 10 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 10 (transLenTr ⟨61, by decide⟩ 10 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_10.D1 (m := 1) from colCertDiv_147_61_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 10 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_10.D2 (m := 1) from colCertDiv_147_61_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_10_match


theorem leaf_147_61_11 (hp : 11 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 11 (transLenTr ⟨61, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 11 (transLenTr ⟨61, by decide⟩ 11 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 11 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 11 (transLenTr ⟨61, by decide⟩ 11 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_11.D1 (m := 1) from colCertDiv_147_61_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 11 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_11.D2 (m := 1) from colCertDiv_147_61_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_11_match


theorem leaf_147_61_12 (hp : 12 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 12 (transLenTr ⟨61, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 12 (transLenTr ⟨61, by decide⟩ 12 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 12 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 12 (transLenTr ⟨61, by decide⟩ 12 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_12.D1 (m := 1) from colCertDiv_147_61_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 12 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_12.D2 (m := 1) from colCertDiv_147_61_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_12_match


theorem leaf_147_61_13 (hp : 13 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 13 (transLenTr ⟨61, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 13 (transLenTr ⟨61, by decide⟩ 13 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 13 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 13 (transLenTr ⟨61, by decide⟩ 13 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_13.D1 (m := 1) from colCertDiv_147_61_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 13 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_13.D2 (m := 1) from colCertDiv_147_61_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_13_match


theorem leaf_147_61_14 (hp : 14 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 14 (transLenTr ⟨61, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 14 (transLenTr ⟨61, by decide⟩ 14 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 14 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 14 (transLenTr ⟨61, by decide⟩ 14 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_14.D1 (m := 1) from colCertDiv_147_61_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 14 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_14.D2 (m := 1) from colCertDiv_147_61_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_14_match


theorem leaf_147_61_15 (hp : 15 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 15 (transLenTr ⟨61, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 15 (transLenTr ⟨61, by decide⟩ 15 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 15 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 15 (transLenTr ⟨61, by decide⟩ 15 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_15.D1 (m := 1) from colCertDiv_147_61_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 15 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_15.D2 (m := 1) from colCertDiv_147_61_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_15_match


theorem leaf_147_61_16 (hp : 16 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 16 (transLenTr ⟨61, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 16 (transLenTr ⟨61, by decide⟩ 16 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 16 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 16 (transLenTr ⟨61, by decide⟩ 16 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_16.D1 (m := 1) from colCertDiv_147_61_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 16 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_16.D2 (m := 1) from colCertDiv_147_61_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_16_match


theorem leaf_147_61_17 (hp : 17 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 17 (transLenTr ⟨61, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 17 (transLenTr ⟨61, by decide⟩ 17 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 17 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 17 (transLenTr ⟨61, by decide⟩ 17 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_17.D1 (m := 1) from colCertDiv_147_61_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 17 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_17.D2 (m := 1) from colCertDiv_147_61_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_17_match


theorem leaf_147_61_18 (hp : 18 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 18 (transLenTr ⟨61, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 18 (transLenTr ⟨61, by decide⟩ 18 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 18 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 18 (transLenTr ⟨61, by decide⟩ 18 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_18.D1 (m := 1) from colCertDiv_147_61_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 18 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_18.D2 (m := 1) from colCertDiv_147_61_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_18_match


theorem leaf_147_61_19 (hp : 19 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 19 (transLenTr ⟨61, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 19 (transLenTr ⟨61, by decide⟩ 19 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 19 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 19 (transLenTr ⟨61, by decide⟩ 19 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_19.D1 (m := 1) from colCertDiv_147_61_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 19 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_19.D2 (m := 1) from colCertDiv_147_61_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_19_match


theorem leaf_147_61_20 (hp : 20 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 20 (transLenTr ⟨61, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 20 (transLenTr ⟨61, by decide⟩ 20 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 20 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 20 (transLenTr ⟨61, by decide⟩ 20 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_20.D1 (m := 1) from colCertDiv_147_61_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 20 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_20.D2 (m := 1) from colCertDiv_147_61_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_20_match


theorem leaf_147_61_21 (hp : 21 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 21 (transLenTr ⟨61, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 21 (transLenTr ⟨61, by decide⟩ 21 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 21 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 21 (transLenTr ⟨61, by decide⟩ 21 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_21.D1 (m := 1) from colCertDiv_147_61_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 21 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_21.D2 (m := 1) from colCertDiv_147_61_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_21_match


theorem leaf_147_61_22 (hp : 22 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 22 (transLenTr ⟨61, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 22 (transLenTr ⟨61, by decide⟩ 22 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 22 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 22 (transLenTr ⟨61, by decide⟩ 22 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_22.D1 (m := 1) from colCertDiv_147_61_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 22 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_22.D2 (m := 1) from colCertDiv_147_61_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_22_match


theorem leaf_147_61_23 (hp : 23 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 23 (transLenTr ⟨61, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 23 (transLenTr ⟨61, by decide⟩ 23 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 23 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 23 (transLenTr ⟨61, by decide⟩ 23 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_23.D1 (m := 1) from colCertDiv_147_61_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 23 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_23.D2 (m := 1) from colCertDiv_147_61_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_23_match


theorem leaf_147_61_24 (hp : 24 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 24 (transLenTr ⟨61, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 24 (transLenTr ⟨61, by decide⟩ 24 hp)) T147_61
      hfix147_61 hinj147_61 hcardT147_61
      (fun i => conj_mem_of_fixedPoints _ _ (T147_61 i) (hfix147_61 i) _)
      ⟨147, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 24 hp) Q2.T147_61_2 Q2.hfix147_61_2 Q2.hinj147_61_2
      Q2.hcardT147_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_61_2 i) (Q2.hfix147_61_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨61, by decide⟩ 24 (transLenTr ⟨61, by decide⟩ 24 hp) : ↥(reps ⟨61, by decide⟩)) : Coordinate 1)
        T147_61 = colFn colCertDiv_147_61_24.D1 (m := 1) from colCertDiv_147_61_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨61, by decide⟩ 24 hp : ↥(Q2.reps ⟨61, by decide⟩)) : Coordinate 2)
        Q2.T147_61_2 = colFn colCertDiv_147_61_24.D2 (m := 1) from colCertDiv_147_61_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_61_24_match


theorem leaf_147_62_0 (hp : 0 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 0 (transLenTr ⟨62, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 0 (transLenTr ⟨62, by decide⟩ 0 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 0 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      colCert_147_62_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_62_1 (hp : 1 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 1 (transLenTr ⟨62, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 1 (transLenTr ⟨62, by decide⟩ 1 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 1 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      colCert_147_62_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_62_2 (hp : 2 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 2 (transLenTr ⟨62, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 2 (transLenTr ⟨62, by decide⟩ 2 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 2 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      colCert_147_62_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_62_3 (hp : 3 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 3 (transLenTr ⟨62, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 3 (transLenTr ⟨62, by decide⟩ 3 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 3 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      colCert_147_62_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_62_4 (hp : 4 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 4 (transLenTr ⟨62, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 4 (transLenTr ⟨62, by decide⟩ 4 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 4 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      colCert_147_62_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_62_5 (hp : 5 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 5 (transLenTr ⟨62, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 5 (transLenTr ⟨62, by decide⟩ 5 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 5 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      colCert_147_62_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_62_6 (hp : 6 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 6 (transLenTr ⟨62, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 6 (transLenTr ⟨62, by decide⟩ 6 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 6 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      colCert_147_62_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_62_7 (hp : 7 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 7 (transLenTr ⟨62, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 7 (transLenTr ⟨62, by decide⟩ 7 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 7 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      colCert_147_62_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_62_8 (hp : 8 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 8 (transLenTr ⟨62, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 8 (transLenTr ⟨62, by decide⟩ 8 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 8 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      colCert_147_62_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_62_9 (hp : 9 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 9 (transLenTr ⟨62, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 9 (transLenTr ⟨62, by decide⟩ 9 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 9 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      colCert_147_62_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_62_10 (hp : 10 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 10 (transLenTr ⟨62, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 10 (transLenTr ⟨62, by decide⟩ 10 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 10 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 10 (transLenTr ⟨62, by decide⟩ 10 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_10.D1 (m := 1) from colCertDiv_147_62_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 10 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_10.D2 (m := 1) from colCertDiv_147_62_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_10_match


theorem leaf_147_62_11 (hp : 11 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 11 (transLenTr ⟨62, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 11 (transLenTr ⟨62, by decide⟩ 11 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 11 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 11 (transLenTr ⟨62, by decide⟩ 11 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_11.D1 (m := 1) from colCertDiv_147_62_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 11 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_11.D2 (m := 1) from colCertDiv_147_62_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_11_match


theorem leaf_147_62_12 (hp : 12 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 12 (transLenTr ⟨62, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 12 (transLenTr ⟨62, by decide⟩ 12 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 12 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 12 (transLenTr ⟨62, by decide⟩ 12 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_12.D1 (m := 1) from colCertDiv_147_62_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 12 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_12.D2 (m := 1) from colCertDiv_147_62_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_12_match


theorem leaf_147_62_13 (hp : 13 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 13 (transLenTr ⟨62, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 13 (transLenTr ⟨62, by decide⟩ 13 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 13 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 13 (transLenTr ⟨62, by decide⟩ 13 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_13.D1 (m := 1) from colCertDiv_147_62_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 13 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_13.D2 (m := 1) from colCertDiv_147_62_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_13_match


theorem leaf_147_62_14 (hp : 14 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 14 (transLenTr ⟨62, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 14 (transLenTr ⟨62, by decide⟩ 14 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 14 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 14 (transLenTr ⟨62, by decide⟩ 14 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_14.D1 (m := 1) from colCertDiv_147_62_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 14 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_14.D2 (m := 1) from colCertDiv_147_62_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_14_match


theorem leaf_147_62_15 (hp : 15 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 15 (transLenTr ⟨62, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 15 (transLenTr ⟨62, by decide⟩ 15 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 15 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 15 (transLenTr ⟨62, by decide⟩ 15 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_15.D1 (m := 1) from colCertDiv_147_62_15.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 15 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_15.D2 (m := 1) from colCertDiv_147_62_15.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_15_match


theorem leaf_147_62_16 (hp : 16 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 16 (transLenTr ⟨62, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 16 (transLenTr ⟨62, by decide⟩ 16 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 16 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 16 (transLenTr ⟨62, by decide⟩ 16 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_16.D1 (m := 1) from colCertDiv_147_62_16.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 16 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_16.D2 (m := 1) from colCertDiv_147_62_16.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_16_match


theorem leaf_147_62_17 (hp : 17 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 17 (transLenTr ⟨62, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 17 (transLenTr ⟨62, by decide⟩ 17 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 17 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 17 (transLenTr ⟨62, by decide⟩ 17 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_17.D1 (m := 1) from colCertDiv_147_62_17.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 17 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_17.D2 (m := 1) from colCertDiv_147_62_17.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_17_match


theorem leaf_147_62_18 (hp : 18 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 18 (transLenTr ⟨62, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 18 (transLenTr ⟨62, by decide⟩ 18 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 18 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 18 (transLenTr ⟨62, by decide⟩ 18 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_18.D1 (m := 1) from colCertDiv_147_62_18.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 18 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_18.D2 (m := 1) from colCertDiv_147_62_18.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_18_match


theorem leaf_147_62_19 (hp : 19 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 19 (transLenTr ⟨62, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 19 (transLenTr ⟨62, by decide⟩ 19 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 19 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 19 (transLenTr ⟨62, by decide⟩ 19 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_19.D1 (m := 1) from colCertDiv_147_62_19.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 19 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_19.D2 (m := 1) from colCertDiv_147_62_19.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_19_match


theorem leaf_147_62_20 (hp : 20 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 20 (transLenTr ⟨62, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 20 (transLenTr ⟨62, by decide⟩ 20 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 20 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 20 (transLenTr ⟨62, by decide⟩ 20 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_20.D1 (m := 1) from colCertDiv_147_62_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 20 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_20.D2 (m := 1) from colCertDiv_147_62_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_20_match


theorem leaf_147_62_21 (hp : 21 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 21 (transLenTr ⟨62, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 21 (transLenTr ⟨62, by decide⟩ 21 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 21 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 21 (transLenTr ⟨62, by decide⟩ 21 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_21.D1 (m := 1) from colCertDiv_147_62_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 21 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_21.D2 (m := 1) from colCertDiv_147_62_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_21_match


theorem leaf_147_62_22 (hp : 22 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 22 (transLenTr ⟨62, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 22 (transLenTr ⟨62, by decide⟩ 22 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 22 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 22 (transLenTr ⟨62, by decide⟩ 22 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_22.D1 (m := 1) from colCertDiv_147_62_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 22 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_22.D2 (m := 1) from colCertDiv_147_62_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_22_match


theorem leaf_147_62_23 (hp : 23 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 23 (transLenTr ⟨62, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 23 (transLenTr ⟨62, by decide⟩ 23 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 23 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 23 (transLenTr ⟨62, by decide⟩ 23 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_23.D1 (m := 1) from colCertDiv_147_62_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 23 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_23.D2 (m := 1) from colCertDiv_147_62_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_23_match


theorem leaf_147_62_24 (hp : 24 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 24 (transLenTr ⟨62, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 24 (transLenTr ⟨62, by decide⟩ 24 hp)) T147_62
      hfix147_62 hinj147_62 hcardT147_62
      (fun i => conj_mem_of_fixedPoints _ _ (T147_62 i) (hfix147_62 i) _)
      ⟨147, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 24 hp) Q2.T147_62_2 Q2.hfix147_62_2 Q2.hinj147_62_2
      Q2.hcardT147_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_62_2 i) (Q2.hfix147_62_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨62, by decide⟩ 24 (transLenTr ⟨62, by decide⟩ 24 hp) : ↥(reps ⟨62, by decide⟩)) : Coordinate 1)
        T147_62 = colFn colCertDiv_147_62_24.D1 (m := 1) from colCertDiv_147_62_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨62, by decide⟩ 24 hp : ↥(Q2.reps ⟨62, by decide⟩)) : Coordinate 2)
        Q2.T147_62_2 = colFn colCertDiv_147_62_24.D2 (m := 1) from colCertDiv_147_62_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_62_24_match


theorem leaf_147_63_0 (hp : 0 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 0 (transLenTr ⟨63, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 0 (transLenTr ⟨63, by decide⟩ 0 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 0 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      colCert_147_63_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_63_1 (hp : 1 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 1 (transLenTr ⟨63, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 1 (transLenTr ⟨63, by decide⟩ 1 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 1 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      colCert_147_63_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_63_2 (hp : 2 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 2 (transLenTr ⟨63, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 2 (transLenTr ⟨63, by decide⟩ 2 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 2 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      colCert_147_63_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_63_3 (hp : 3 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 3 (transLenTr ⟨63, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 3 (transLenTr ⟨63, by decide⟩ 3 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 3 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      colCert_147_63_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_63_4 (hp : 4 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 4 (transLenTr ⟨63, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 4 (transLenTr ⟨63, by decide⟩ 4 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 4 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      colCert_147_63_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_63_5 (hp : 5 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 5 (transLenTr ⟨63, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 5 (transLenTr ⟨63, by decide⟩ 5 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 5 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 5 (transLenTr ⟨63, by decide⟩ 5 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_5.D1 (m := 1) from colCertDiv_147_63_5.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 5 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_5.D2 (m := 1) from colCertDiv_147_63_5.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_5_match


theorem leaf_147_63_6 (hp : 6 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 6 (transLenTr ⟨63, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 6 (transLenTr ⟨63, by decide⟩ 6 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 6 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 6 (transLenTr ⟨63, by decide⟩ 6 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_6.D1 (m := 1) from colCertDiv_147_63_6.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 6 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_6.D2 (m := 1) from colCertDiv_147_63_6.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_6_match


theorem leaf_147_63_7 (hp : 7 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 7 (transLenTr ⟨63, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 7 (transLenTr ⟨63, by decide⟩ 7 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 7 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 7 (transLenTr ⟨63, by decide⟩ 7 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_7.D1 (m := 1) from colCertDiv_147_63_7.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 7 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_7.D2 (m := 1) from colCertDiv_147_63_7.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_7_match


theorem leaf_147_63_8 (hp : 8 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 8 (transLenTr ⟨63, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 8 (transLenTr ⟨63, by decide⟩ 8 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 8 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 8 (transLenTr ⟨63, by decide⟩ 8 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_8.D1 (m := 1) from colCertDiv_147_63_8.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 8 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_8.D2 (m := 1) from colCertDiv_147_63_8.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_8_match


theorem leaf_147_63_9 (hp : 9 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 9 (transLenTr ⟨63, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 9 (transLenTr ⟨63, by decide⟩ 9 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 9 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 9 (transLenTr ⟨63, by decide⟩ 9 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_9.D1 (m := 1) from colCertDiv_147_63_9.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 9 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_9.D2 (m := 1) from colCertDiv_147_63_9.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_9_match


theorem leaf_147_63_10 (hp : 10 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 10 (transLenTr ⟨63, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 10 (transLenTr ⟨63, by decide⟩ 10 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 10 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 10 (transLenTr ⟨63, by decide⟩ 10 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_10.D1 (m := 1) from colCertDiv_147_63_10.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 10 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_10.D2 (m := 1) from colCertDiv_147_63_10.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_10_match


theorem leaf_147_63_11 (hp : 11 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 11 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 11 (transLenTr ⟨63, by decide⟩ 11 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 11 (transLenTr ⟨63, by decide⟩ 11 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 11 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 11 (transLenTr ⟨63, by decide⟩ 11 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_11.D1 (m := 1) from colCertDiv_147_63_11.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 11 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_11.D2 (m := 1) from colCertDiv_147_63_11.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_11_match


theorem leaf_147_63_12 (hp : 12 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 12 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 12 (transLenTr ⟨63, by decide⟩ 12 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 12 (transLenTr ⟨63, by decide⟩ 12 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 12 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 12 (transLenTr ⟨63, by decide⟩ 12 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_12.D1 (m := 1) from colCertDiv_147_63_12.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 12 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_12.D2 (m := 1) from colCertDiv_147_63_12.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_12_match


theorem leaf_147_63_13 (hp : 13 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 13 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 13 (transLenTr ⟨63, by decide⟩ 13 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 13 (transLenTr ⟨63, by decide⟩ 13 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 13 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 13 (transLenTr ⟨63, by decide⟩ 13 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_13.D1 (m := 1) from colCertDiv_147_63_13.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 13 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_13.D2 (m := 1) from colCertDiv_147_63_13.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_13_match


theorem leaf_147_63_14 (hp : 14 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 14 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 14 (transLenTr ⟨63, by decide⟩ 14 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 14 (transLenTr ⟨63, by decide⟩ 14 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 14 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 14 (transLenTr ⟨63, by decide⟩ 14 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_14.D1 (m := 1) from colCertDiv_147_63_14.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 14 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_14.D2 (m := 1) from colCertDiv_147_63_14.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_14_match


theorem leaf_147_63_15 (hp : 15 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 15 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 15 (transLenTr ⟨63, by decide⟩ 15 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 15 (transLenTr ⟨63, by decide⟩ 15 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 15 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      colCert_147_63_15.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_63_16 (hp : 16 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 16 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 16 (transLenTr ⟨63, by decide⟩ 16 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 16 (transLenTr ⟨63, by decide⟩ 16 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 16 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      colCert_147_63_16.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_63_17 (hp : 17 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 17 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 17 (transLenTr ⟨63, by decide⟩ 17 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 17 (transLenTr ⟨63, by decide⟩ 17 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 17 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      colCert_147_63_17.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_63_18 (hp : 18 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 18 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 18 (transLenTr ⟨63, by decide⟩ 18 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 18 (transLenTr ⟨63, by decide⟩ 18 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 18 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      colCert_147_63_18.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_63_19 (hp : 19 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 19 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 19 (transLenTr ⟨63, by decide⟩ 19 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 19 (transLenTr ⟨63, by decide⟩ 19 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 19 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      colCert_147_63_19.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_63_20 (hp : 20 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 20 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 20 (transLenTr ⟨63, by decide⟩ 20 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 20 (transLenTr ⟨63, by decide⟩ 20 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 20 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 20 (transLenTr ⟨63, by decide⟩ 20 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_20.D1 (m := 1) from colCertDiv_147_63_20.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 20 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_20.D2 (m := 1) from colCertDiv_147_63_20.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_20_match


theorem leaf_147_63_21 (hp : 21 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 21 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 21 (transLenTr ⟨63, by decide⟩ 21 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 21 (transLenTr ⟨63, by decide⟩ 21 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 21 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 21 (transLenTr ⟨63, by decide⟩ 21 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_21.D1 (m := 1) from colCertDiv_147_63_21.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 21 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_21.D2 (m := 1) from colCertDiv_147_63_21.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_21_match


theorem leaf_147_63_22 (hp : 22 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 22 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 22 (transLenTr ⟨63, by decide⟩ 22 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 22 (transLenTr ⟨63, by decide⟩ 22 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 22 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 22 (transLenTr ⟨63, by decide⟩ 22 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_22.D1 (m := 1) from colCertDiv_147_63_22.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 22 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_22.D2 (m := 1) from colCertDiv_147_63_22.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_22_match


theorem leaf_147_63_23 (hp : 23 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 23 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 23 (transLenTr ⟨63, by decide⟩ 23 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 23 (transLenTr ⟨63, by decide⟩ 23 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 23 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 23 (transLenTr ⟨63, by decide⟩ 23 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_23.D1 (m := 1) from colCertDiv_147_63_23.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 23 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_23.D2 (m := 1) from colCertDiv_147_63_23.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_23_match


theorem leaf_147_63_24 (hp : 24 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 24 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 24 (transLenTr ⟨63, by decide⟩ 24 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨147, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 24 (transLenTr ⟨63, by decide⟩ 24 hp)) T147_63
      hfix147_63 hinj147_63 hcardT147_63
      (fun i => conj_mem_of_fixedPoints _ _ (T147_63 i) (hfix147_63 i) _)
      ⟨147, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 24 hp) Q2.T147_63_2 Q2.hfix147_63_2 Q2.hinj147_63_2
      Q2.hcardT147_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_63_2 i) (Q2.hfix147_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨147, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 24 (transLenTr ⟨63, by decide⟩ 24 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T147_63 = colFn colCertDiv_147_63_24.D1 (m := 1) from colCertDiv_147_63_24.bind1,
    show colData2 (⟨147, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 24 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T147_63_2 = colFn colCertDiv_147_63_24.D2 (m := 1) from colCertDiv_147_63_24.bind2]
  rw [alnId_147 j hj]
  exact fastcode_of_div ⟨147, by decide⟩ _ _ _
    ((alnId_147 j hj) ▸ Q2.listedAt (⟨147, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨147, by decide⟩ : Fin 148) hj hq).1) colCertDiv_147_63_24_match


theorem leaf_147_64_0 (hp : 0 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 0 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 0 (transLenTr ⟨64, by decide⟩ 0 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 0 (transLenTr ⟨64, by decide⟩ 0 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 0 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_0.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_1 (hp : 1 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 1 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 1 (transLenTr ⟨64, by decide⟩ 1 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 1 (transLenTr ⟨64, by decide⟩ 1 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 1 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_1.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_2 (hp : 2 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 2 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 2 (transLenTr ⟨64, by decide⟩ 2 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 2 (transLenTr ⟨64, by decide⟩ 2 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 2 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_2.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_3 (hp : 3 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 3 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 3 (transLenTr ⟨64, by decide⟩ 3 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 3 (transLenTr ⟨64, by decide⟩ 3 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 3 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_3.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_4 (hp : 4 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 4 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 4 (transLenTr ⟨64, by decide⟩ 4 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 4 (transLenTr ⟨64, by decide⟩ 4 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 4 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_4.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_5 (hp : 5 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 5 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 5 (transLenTr ⟨64, by decide⟩ 5 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 5 (transLenTr ⟨64, by decide⟩ 5 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 5 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_5.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_6 (hp : 6 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 6 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 6 (transLenTr ⟨64, by decide⟩ 6 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 6 (transLenTr ⟨64, by decide⟩ 6 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 6 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_6.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_7 (hp : 7 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 7 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 7 (transLenTr ⟨64, by decide⟩ 7 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 7 (transLenTr ⟨64, by decide⟩ 7 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 7 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_7.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_8 (hp : 8 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 8 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 8 (transLenTr ⟨64, by decide⟩ 8 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 8 (transLenTr ⟨64, by decide⟩ 8 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 8 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_8.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_9 (hp : 9 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 9 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 9 (transLenTr ⟨64, by decide⟩ 9 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 9 (transLenTr ⟨64, by decide⟩ 9 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 9 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_9.hD ?_).symm
  rw [alnId_147 j hj]


theorem leaf_147_64_10 (hp : 10 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 147 []).length)
    (hq : (normIsRep.getD 147 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 10 hp)
        (rowE2 (⟨147, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 10 (transLenTr ⟨64, by decide⟩ 10 hp))
        (rowE1 (⟨147, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨147, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨147, by decide⟩ (listedAt ⟨147, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 10 (transLenTr ⟨64, by decide⟩ 10 hp)) T147_64
      hfix147_64 hinj147_64 hcardT147_64
      (fun i => conj_mem_of_fixedPoints _ _ (T147_64 i) (hfix147_64 i) _)
      ⟨147, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨147, by decide⟩ (Q2.listedAt ⟨147, by decide⟩
        (alnCheck_rep ⟨147, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 10 hp) Q2.T147_64_2 Q2.hfix147_64_2 Q2.hinj147_64_2
      Q2.hcardT147_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T147_64_2 i) (Q2.hfix147_64_2 i) _)
      colCert_147_64_10.hD ?_).symm
  rw [alnId_147 j hj]


end LeanDring.P5Presentation
