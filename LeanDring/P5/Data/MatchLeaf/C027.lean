/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C005
import LeanDring.P5.Data.ColRestCheap.C035
import LeanDring.P5.Data.ColRestCheap.C036
import LeanDring.P5.Data.ColRestCheap.C037
import LeanDring.P5.Data.ColRestCheap.C038
import LeanDring.P5.Data.ColTau.C001
import LeanDring.P5.Data.EntryK.C027
import LeanDring.P5.Data.EntryK.C028
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C050
import LeanDring.P5.Data.SpeciesDiv.C051
import LeanDring.P5.Data.SpeciesDiv.C052
import LeanDring.P5.Data.SpeciesDiv.C053
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk02

/-! # Stage-5 leaves, chunk 26 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_118_118_9 (hp : 9 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 9 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 9 (transLenTr ⟨118, by decide⟩ 9 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 9 (transLenTr ⟨118, by decide⟩ 9 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 9 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_9.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_10 (hp : 10 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 10 (transLenTr ⟨118, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 10 (transLenTr ⟨118, by decide⟩ 10 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 10 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_11 (hp : 11 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 11 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 11 (transLenTr ⟨118, by decide⟩ 11 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 11 (transLenTr ⟨118, by decide⟩ 11 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 11 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_11.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_12 (hp : 12 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 12 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 12 (transLenTr ⟨118, by decide⟩ 12 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 12 (transLenTr ⟨118, by decide⟩ 12 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 12 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_12.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_13 (hp : 13 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 13 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 13 (transLenTr ⟨118, by decide⟩ 13 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 13 (transLenTr ⟨118, by decide⟩ 13 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 13 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_13.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_14 (hp : 14 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 14 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 14 (transLenTr ⟨118, by decide⟩ 14 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 14 (transLenTr ⟨118, by decide⟩ 14 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 14 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_14.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_15 (hp : 15 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 15 (transLenTr ⟨118, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 15 (transLenTr ⟨118, by decide⟩ 15 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 15 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_16 (hp : 16 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 16 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 16 (transLenTr ⟨118, by decide⟩ 16 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 16 (transLenTr ⟨118, by decide⟩ 16 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 16 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_16.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_17 (hp : 17 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 17 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 17 (transLenTr ⟨118, by decide⟩ 17 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 17 (transLenTr ⟨118, by decide⟩ 17 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 17 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_17.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_18 (hp : 18 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 18 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 18 (transLenTr ⟨118, by decide⟩ 18 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 18 (transLenTr ⟨118, by decide⟩ 18 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 18 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_18.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_19 (hp : 19 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 19 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 19 (transLenTr ⟨118, by decide⟩ 19 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 19 (transLenTr ⟨118, by decide⟩ 19 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 19 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_19.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_20 (hp : 20 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 20 (transLenTr ⟨118, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 20 (transLenTr ⟨118, by decide⟩ 20 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 20 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_21 (hp : 21 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 21 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 21 (transLenTr ⟨118, by decide⟩ 21 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 21 (transLenTr ⟨118, by decide⟩ 21 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 21 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_21.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_22 (hp : 22 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 22 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 22 (transLenTr ⟨118, by decide⟩ 22 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 22 (transLenTr ⟨118, by decide⟩ 22 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 22 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_22.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_23 (hp : 23 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 23 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 23 (transLenTr ⟨118, by decide⟩ 23 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 23 (transLenTr ⟨118, by decide⟩ 23 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 23 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_23.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_24 (hp : 24 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 24 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 24 (transLenTr ⟨118, by decide⟩ 24 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 24 (transLenTr ⟨118, by decide⟩ 24 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 24 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_24.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_25 (hp : 25 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 25 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 25 (transLenTr ⟨118, by decide⟩ 25 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 25 (transLenTr ⟨118, by decide⟩ 25 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 25 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_25.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_30 (hp : 30 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 30 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 30 (transLenTr ⟨118, by decide⟩ 30 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 30 (transLenTr ⟨118, by decide⟩ 30 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 30 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_30.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_35 (hp : 35 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 35 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 35 (transLenTr ⟨118, by decide⟩ 35 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 35 (transLenTr ⟨118, by decide⟩ 35 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 35 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_35.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_40 (hp : 40 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 40 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 40 (transLenTr ⟨118, by decide⟩ 40 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 40 (transLenTr ⟨118, by decide⟩ 40 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 40 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_40.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_45 (hp : 45 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 45 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 45 (transLenTr ⟨118, by decide⟩ 45 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 45 (transLenTr ⟨118, by decide⟩ 45 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 45 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_45.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_50 (hp : 50 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 50 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 50 (transLenTr ⟨118, by decide⟩ 50 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 50 (transLenTr ⟨118, by decide⟩ 50 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 50 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_50.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_55 (hp : 55 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 55 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 55 (transLenTr ⟨118, by decide⟩ 55 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 55 (transLenTr ⟨118, by decide⟩ 55 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 55 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_55.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_60 (hp : 60 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 60 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 60 (transLenTr ⟨118, by decide⟩ 60 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 60 (transLenTr ⟨118, by decide⟩ 60 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 60 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_60.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_65 (hp : 65 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 65 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 65 (transLenTr ⟨118, by decide⟩ 65 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 65 (transLenTr ⟨118, by decide⟩ 65 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 65 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_65.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_70 (hp : 70 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 70 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 70 (transLenTr ⟨118, by decide⟩ 70 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 70 (transLenTr ⟨118, by decide⟩ 70 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 70 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_70.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_75 (hp : 75 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 75 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 75 (transLenTr ⟨118, by decide⟩ 75 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 75 (transLenTr ⟨118, by decide⟩ 75 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 75 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_75.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_80 (hp : 80 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 80 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 80 (transLenTr ⟨118, by decide⟩ 80 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 80 (transLenTr ⟨118, by decide⟩ 80 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 80 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_80.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_85 (hp : 85 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 85 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 85 (transLenTr ⟨118, by decide⟩ 85 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 85 (transLenTr ⟨118, by decide⟩ 85 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 85 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_85.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_90 (hp : 90 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 90 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 90 (transLenTr ⟨118, by decide⟩ 90 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 90 (transLenTr ⟨118, by decide⟩ 90 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 90 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_90.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_95 (hp : 95 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 95 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 95 (transLenTr ⟨118, by decide⟩ 95 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 95 (transLenTr ⟨118, by decide⟩ 95 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 95 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_95.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_100 (hp : 100 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 100 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 100 (transLenTr ⟨118, by decide⟩ 100 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 100 (transLenTr ⟨118, by decide⟩ 100 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 100 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_100.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_105 (hp : 105 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 105 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 105 (transLenTr ⟨118, by decide⟩ 105 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 105 (transLenTr ⟨118, by decide⟩ 105 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 105 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_105.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_110 (hp : 110 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 110 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 110 (transLenTr ⟨118, by decide⟩ 110 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 110 (transLenTr ⟨118, by decide⟩ 110 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 110 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_110.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_115 (hp : 115 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 115 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 115 (transLenTr ⟨118, by decide⟩ 115 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 115 (transLenTr ⟨118, by decide⟩ 115 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 115 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_115.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_118_120 (hp : 120 < (Q2.transData.getD 118 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨118, by decide⟩ : Fin 148)) (colE2 ⟨118, by decide⟩ 120 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨118, by decide⟩ : Fin 148))
        (colE1 ⟨118, by decide⟩ 120 (transLenTr ⟨118, by decide⟩ 120 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨118, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨118, by decide⟩ 120 (transLenTr ⟨118, by decide⟩ 120 hp)) T118_118
      hfix118_118 hinj118_118 hcardT118_118
      (fun i => conj_mem_of_fixedPoints _ _ (T118_118 i) (hfix118_118 i) _)
      ⟨118, by decide⟩ ⟨118, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨118, by decide⟩ 120 hp) Q2.T118_118_2 Q2.hfix118_118_2 Q2.hinj118_118_2
      Q2.hcardT118_118_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_118_2 i) (Q2.hfix118_118_2 i) _)
      colCert_118_118_120.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_119_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T119_1
      hfix119_1 hinj119_1 hcardT119_1
      (fun i => conj_mem_of_fixedPoints _ _ (T119_1 i) (hfix119_1 i) _)
      ⟨119, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T119_1_2 Q2.hfix119_1_2 Q2.hinj119_1_2
      Q2.hcardT119_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_1_2 i) (Q2.hfix119_1_2 i) _)
      colCert_119_1_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T119_1
      hfix119_1 hinj119_1 hcardT119_1
      (fun i => conj_mem_of_fixedPoints _ _ (T119_1 i) (hfix119_1 i) _)
      ⟨119, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T119_1_2 Q2.hfix119_1_2 Q2.hinj119_1_2
      Q2.hcardT119_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_1_2 i) (Q2.hfix119_1_2 i) _)
      colCert_119_1_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T119_1
      hfix119_1 hinj119_1 hcardT119_1
      (fun i => conj_mem_of_fixedPoints _ _ (T119_1 i) (hfix119_1 i) _)
      ⟨119, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T119_1_2 Q2.hfix119_1_2 Q2.hinj119_1_2
      Q2.hcardT119_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_1_2 i) (Q2.hfix119_1_2 i) _)
      colCert_119_1_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T119_1
      hfix119_1 hinj119_1 hcardT119_1
      (fun i => conj_mem_of_fixedPoints _ _ (T119_1 i) (hfix119_1 i) _)
      ⟨119, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T119_1_2 Q2.hfix119_1_2 Q2.hinj119_1_2
      Q2.hcardT119_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_1_2 i) (Q2.hfix119_1_2 i) _)
      colCert_119_1_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T119_1
      hfix119_1 hinj119_1 hcardT119_1
      (fun i => conj_mem_of_fixedPoints _ _ (T119_1 i) (hfix119_1 i) _)
      ⟨119, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T119_1_2 Q2.hfix119_1_2 Q2.hinj119_1_2
      Q2.hcardT119_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_1_2 i) (Q2.hfix119_1_2 i) _)
      colCert_119_1_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T119_6
      hfix119_6 hinj119_6 hcardT119_6
      (fun i => conj_mem_of_fixedPoints _ _ (T119_6 i) (hfix119_6 i) _)
      ⟨119, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T119_6_2 Q2.hfix119_6_2 Q2.hinj119_6_2
      Q2.hcardT119_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_6_2 i) (Q2.hfix119_6_2 i) _)
      colCert_119_6_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T119_6
      hfix119_6 hinj119_6 hcardT119_6
      (fun i => conj_mem_of_fixedPoints _ _ (T119_6 i) (hfix119_6 i) _)
      ⟨119, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T119_6_2 Q2.hfix119_6_2 Q2.hinj119_6_2
      Q2.hcardT119_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_6_2 i) (Q2.hfix119_6_2 i) _)
      colCert_119_6_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T119_6
      hfix119_6 hinj119_6 hcardT119_6
      (fun i => conj_mem_of_fixedPoints _ _ (T119_6 i) (hfix119_6 i) _)
      ⟨119, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T119_6_2 Q2.hfix119_6_2 Q2.hinj119_6_2
      Q2.hcardT119_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_6_2 i) (Q2.hfix119_6_2 i) _)
      colCert_119_6_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T119_6
      hfix119_6 hinj119_6 hcardT119_6
      (fun i => conj_mem_of_fixedPoints _ _ (T119_6 i) (hfix119_6 i) _)
      ⟨119, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T119_6_2 Q2.hfix119_6_2 Q2.hinj119_6_2
      Q2.hcardT119_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_6_2 i) (Q2.hfix119_6_2 i) _)
      colCert_119_6_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T119_6
      hfix119_6 hinj119_6 hcardT119_6
      (fun i => conj_mem_of_fixedPoints _ _ (T119_6 i) (hfix119_6 i) _)
      ⟨119, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T119_6_2 Q2.hfix119_6_2 Q2.hinj119_6_2
      Q2.hcardT119_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_6_2 i) (Q2.hfix119_6_2 i) _)
      colCert_119_6_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T119_7
      hfix119_7 hinj119_7 hcardT119_7
      (fun i => conj_mem_of_fixedPoints _ _ (T119_7 i) (hfix119_7 i) _)
      ⟨119, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T119_7_2 Q2.hfix119_7_2 Q2.hinj119_7_2
      Q2.hcardT119_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_7_2 i) (Q2.hfix119_7_2 i) _)
      colCert_119_7_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T119_7
      hfix119_7 hinj119_7 hcardT119_7
      (fun i => conj_mem_of_fixedPoints _ _ (T119_7 i) (hfix119_7 i) _)
      ⟨119, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T119_7_2 Q2.hfix119_7_2 Q2.hinj119_7_2
      Q2.hcardT119_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_7_2 i) (Q2.hfix119_7_2 i) _)
      colCert_119_7_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T119_7
      hfix119_7 hinj119_7 hcardT119_7
      (fun i => conj_mem_of_fixedPoints _ _ (T119_7 i) (hfix119_7 i) _)
      ⟨119, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T119_7_2 Q2.hfix119_7_2 Q2.hinj119_7_2
      Q2.hcardT119_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_7_2 i) (Q2.hfix119_7_2 i) _)
      colCert_119_7_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T119_7
      hfix119_7 hinj119_7 hcardT119_7
      (fun i => conj_mem_of_fixedPoints _ _ (T119_7 i) (hfix119_7 i) _)
      ⟨119, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T119_7_2 Q2.hfix119_7_2 Q2.hinj119_7_2
      Q2.hcardT119_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_7_2 i) (Q2.hfix119_7_2 i) _)
      colCert_119_7_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T119_7
      hfix119_7 hinj119_7 hcardT119_7
      (fun i => conj_mem_of_fixedPoints _ _ (T119_7 i) (hfix119_7 i) _)
      ⟨119, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T119_7_2 Q2.hfix119_7_2 Q2.hinj119_7_2
      Q2.hcardT119_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_7_2 i) (Q2.hfix119_7_2 i) _)
      colCert_119_7_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T119_8
      hfix119_8 hinj119_8 hcardT119_8
      (fun i => conj_mem_of_fixedPoints _ _ (T119_8 i) (hfix119_8 i) _)
      ⟨119, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T119_8_2 Q2.hfix119_8_2 Q2.hinj119_8_2
      Q2.hcardT119_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_8_2 i) (Q2.hfix119_8_2 i) _)
      colCert_119_8_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T119_8
      hfix119_8 hinj119_8 hcardT119_8
      (fun i => conj_mem_of_fixedPoints _ _ (T119_8 i) (hfix119_8 i) _)
      ⟨119, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T119_8_2 Q2.hfix119_8_2 Q2.hinj119_8_2
      Q2.hcardT119_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_8_2 i) (Q2.hfix119_8_2 i) _)
      colCert_119_8_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T119_8
      hfix119_8 hinj119_8 hcardT119_8
      (fun i => conj_mem_of_fixedPoints _ _ (T119_8 i) (hfix119_8 i) _)
      ⟨119, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T119_8_2 Q2.hfix119_8_2 Q2.hinj119_8_2
      Q2.hcardT119_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_8_2 i) (Q2.hfix119_8_2 i) _)
      colCert_119_8_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T119_8
      hfix119_8 hinj119_8 hcardT119_8
      (fun i => conj_mem_of_fixedPoints _ _ (T119_8 i) (hfix119_8 i) _)
      ⟨119, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T119_8_2 Q2.hfix119_8_2 Q2.hinj119_8_2
      Q2.hcardT119_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_8_2 i) (Q2.hfix119_8_2 i) _)
      colCert_119_8_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T119_8
      hfix119_8 hinj119_8 hcardT119_8
      (fun i => conj_mem_of_fixedPoints _ _ (T119_8 i) (hfix119_8 i) _)
      ⟨119, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T119_8_2 Q2.hfix119_8_2 Q2.hinj119_8_2
      Q2.hcardT119_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_8_2 i) (Q2.hfix119_8_2 i) _)
      colCert_119_8_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T119_9
      hfix119_9 hinj119_9 hcardT119_9
      (fun i => conj_mem_of_fixedPoints _ _ (T119_9 i) (hfix119_9 i) _)
      ⟨119, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T119_9_2 Q2.hfix119_9_2 Q2.hinj119_9_2
      Q2.hcardT119_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_9_2 i) (Q2.hfix119_9_2 i) _)
      colCert_119_9_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T119_9
      hfix119_9 hinj119_9 hcardT119_9
      (fun i => conj_mem_of_fixedPoints _ _ (T119_9 i) (hfix119_9 i) _)
      ⟨119, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T119_9_2 Q2.hfix119_9_2 Q2.hinj119_9_2
      Q2.hcardT119_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_9_2 i) (Q2.hfix119_9_2 i) _)
      colCert_119_9_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T119_9
      hfix119_9 hinj119_9 hcardT119_9
      (fun i => conj_mem_of_fixedPoints _ _ (T119_9 i) (hfix119_9 i) _)
      ⟨119, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T119_9_2 Q2.hfix119_9_2 Q2.hinj119_9_2
      Q2.hcardT119_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_9_2 i) (Q2.hfix119_9_2 i) _)
      colCert_119_9_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T119_9
      hfix119_9 hinj119_9 hcardT119_9
      (fun i => conj_mem_of_fixedPoints _ _ (T119_9 i) (hfix119_9 i) _)
      ⟨119, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T119_9_2 Q2.hfix119_9_2 Q2.hinj119_9_2
      Q2.hcardT119_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_9_2 i) (Q2.hfix119_9_2 i) _)
      colCert_119_9_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T119_9
      hfix119_9 hinj119_9 hcardT119_9
      (fun i => conj_mem_of_fixedPoints _ _ (T119_9 i) (hfix119_9 i) _)
      ⟨119, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T119_9_2 Q2.hfix119_9_2 Q2.hinj119_9_2
      Q2.hcardT119_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_9_2 i) (Q2.hfix119_9_2 i) _)
      colCert_119_9_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T119_10
      hfix119_10 hinj119_10 hcardT119_10
      (fun i => conj_mem_of_fixedPoints _ _ (T119_10 i) (hfix119_10 i) _)
      ⟨119, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T119_10_2 Q2.hfix119_10_2 Q2.hinj119_10_2
      Q2.hcardT119_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_10_2 i) (Q2.hfix119_10_2 i) _)
      colCert_119_10_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T119_10
      hfix119_10 hinj119_10 hcardT119_10
      (fun i => conj_mem_of_fixedPoints _ _ (T119_10 i) (hfix119_10 i) _)
      ⟨119, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T119_10_2 Q2.hfix119_10_2 Q2.hinj119_10_2
      Q2.hcardT119_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_10_2 i) (Q2.hfix119_10_2 i) _)
      colCert_119_10_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T119_10
      hfix119_10 hinj119_10 hcardT119_10
      (fun i => conj_mem_of_fixedPoints _ _ (T119_10 i) (hfix119_10 i) _)
      ⟨119, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T119_10_2 Q2.hfix119_10_2 Q2.hinj119_10_2
      Q2.hcardT119_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_10_2 i) (Q2.hfix119_10_2 i) _)
      colCert_119_10_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T119_10
      hfix119_10 hinj119_10 hcardT119_10
      (fun i => conj_mem_of_fixedPoints _ _ (T119_10 i) (hfix119_10 i) _)
      ⟨119, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T119_10_2 Q2.hfix119_10_2 Q2.hinj119_10_2
      Q2.hcardT119_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_10_2 i) (Q2.hfix119_10_2 i) _)
      colCert_119_10_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T119_10
      hfix119_10 hinj119_10 hcardT119_10
      (fun i => conj_mem_of_fixedPoints _ _ (T119_10 i) (hfix119_10 i) _)
      ⟨119, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T119_10_2 Q2.hfix119_10_2 Q2.hinj119_10_2
      Q2.hcardT119_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_10_2 i) (Q2.hfix119_10_2 i) _)
      colCert_119_10_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T119_12
      hfix119_12 hinj119_12 hcardT119_12
      (fun i => conj_mem_of_fixedPoints _ _ (T119_12 i) (hfix119_12 i) _)
      ⟨119, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T119_12_2 Q2.hfix119_12_2 Q2.hinj119_12_2
      Q2.hcardT119_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_12_2 i) (Q2.hfix119_12_2 i) _)
      colCert_119_12_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T119_12
      hfix119_12 hinj119_12 hcardT119_12
      (fun i => conj_mem_of_fixedPoints _ _ (T119_12 i) (hfix119_12 i) _)
      ⟨119, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T119_12_2 Q2.hfix119_12_2 Q2.hinj119_12_2
      Q2.hcardT119_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_12_2 i) (Q2.hfix119_12_2 i) _)
      colCert_119_12_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T119_12
      hfix119_12 hinj119_12 hcardT119_12
      (fun i => conj_mem_of_fixedPoints _ _ (T119_12 i) (hfix119_12 i) _)
      ⟨119, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T119_12_2 Q2.hfix119_12_2 Q2.hinj119_12_2
      Q2.hcardT119_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_12_2 i) (Q2.hfix119_12_2 i) _)
      colCert_119_12_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T119_12
      hfix119_12 hinj119_12 hcardT119_12
      (fun i => conj_mem_of_fixedPoints _ _ (T119_12 i) (hfix119_12 i) _)
      ⟨119, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T119_12_2 Q2.hfix119_12_2 Q2.hinj119_12_2
      Q2.hcardT119_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_12_2 i) (Q2.hfix119_12_2 i) _)
      colCert_119_12_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T119_12
      hfix119_12 hinj119_12 hcardT119_12
      (fun i => conj_mem_of_fixedPoints _ _ (T119_12 i) (hfix119_12 i) _)
      ⟨119, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T119_12_2 Q2.hfix119_12_2 Q2.hinj119_12_2
      Q2.hcardT119_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_12_2 i) (Q2.hfix119_12_2 i) _)
      colCert_119_12_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_0 (hp : 0 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 0 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_1 (hp : 1 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 1 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_2 (hp : 2 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 2 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_3 (hp : 3 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 3 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_4 (hp : 4 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 4 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_5 (hp : 5 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 5 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T119_13 = colFn colCertDiv_119_13_5.D1 (m := 5) from colCertDiv_119_13_5.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 5 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T119_13_2 = colFn colCertDiv_119_13_5.D2 (m := 5) from colCertDiv_119_13_5.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_tau ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_13_5_tau_match


theorem leaf_119_13_6 (hp : 6 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 6 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 6 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T119_13 = colFn colCertDiv_119_13_6.D1 (m := 5) from colCertDiv_119_13_6.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 6 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T119_13_2 = colFn colCertDiv_119_13_6.D2 (m := 5) from colCertDiv_119_13_6.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_tau ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_13_6_tau_match


theorem leaf_119_13_7 (hp : 7 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 7 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 7 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T119_13 = colFn colCertDiv_119_13_7.D1 (m := 5) from colCertDiv_119_13_7.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 7 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T119_13_2 = colFn colCertDiv_119_13_7.D2 (m := 5) from colCertDiv_119_13_7.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_tau ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_13_7_tau_match


theorem leaf_119_13_8 (hp : 8 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 8 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 8 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T119_13 = colFn colCertDiv_119_13_8.D1 (m := 5) from colCertDiv_119_13_8.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 8 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T119_13_2 = colFn colCertDiv_119_13_8.D2 (m := 5) from colCertDiv_119_13_8.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_tau ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_13_8_tau_match


theorem leaf_119_13_9 (hp : 9 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 9 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 9 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_9.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_10 (hp : 10 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 10 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_11 (hp : 11 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 11 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 11 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_11.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_12 (hp : 12 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 12 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 12 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_12.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_13 (hp : 13 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 13 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 13 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_13.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_14 (hp : 14 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 14 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 14 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_14.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_15 (hp : 15 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 15 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_16 (hp : 16 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 16 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 16 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_16.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_17 (hp : 17 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 17 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 17 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_17.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_18 (hp : 18 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 18 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 18 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_18.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_19 (hp : 19 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 19 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 19 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_19.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_20 (hp : 20 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 20 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_21 (hp : 21 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 21 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 21 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_21.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_22 (hp : 22 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 22 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 22 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_22.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_23 (hp : 23 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 23 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 23 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_23.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_13_24 (hp : 24 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 24 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp)) T119_13
      hfix119_13 hinj119_13 hcardT119_13
      (fun i => conj_mem_of_fixedPoints _ _ (T119_13 i) (hfix119_13 i) _)
      ⟨119, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 24 hp) Q2.T119_13_2 Q2.hfix119_13_2 Q2.hinj119_13_2
      Q2.hcardT119_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_13_2 i) (Q2.hfix119_13_2 i) _)
      colCert_119_13_24.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T119_19
      hfix119_19 hinj119_19 hcardT119_19
      (fun i => conj_mem_of_fixedPoints _ _ (T119_19 i) (hfix119_19 i) _)
      ⟨119, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T119_19_2 Q2.hfix119_19_2 Q2.hinj119_19_2
      Q2.hcardT119_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_19_2 i) (Q2.hfix119_19_2 i) _)
      colCert_119_19_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T119_19
      hfix119_19 hinj119_19 hcardT119_19
      (fun i => conj_mem_of_fixedPoints _ _ (T119_19 i) (hfix119_19 i) _)
      ⟨119, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T119_19_2 Q2.hfix119_19_2 Q2.hinj119_19_2
      Q2.hcardT119_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_19_2 i) (Q2.hfix119_19_2 i) _)
      colCert_119_19_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T119_19
      hfix119_19 hinj119_19 hcardT119_19
      (fun i => conj_mem_of_fixedPoints _ _ (T119_19 i) (hfix119_19 i) _)
      ⟨119, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T119_19_2 Q2.hfix119_19_2 Q2.hinj119_19_2
      Q2.hcardT119_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_19_2 i) (Q2.hfix119_19_2 i) _)
      colCert_119_19_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T119_19
      hfix119_19 hinj119_19 hcardT119_19
      (fun i => conj_mem_of_fixedPoints _ _ (T119_19 i) (hfix119_19 i) _)
      ⟨119, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T119_19_2 Q2.hfix119_19_2 Q2.hinj119_19_2
      Q2.hcardT119_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_19_2 i) (Q2.hfix119_19_2 i) _)
      colCert_119_19_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T119_19
      hfix119_19 hinj119_19 hcardT119_19
      (fun i => conj_mem_of_fixedPoints _ _ (T119_19 i) (hfix119_19 i) _)
      ⟨119, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T119_19_2 Q2.hfix119_19_2 Q2.hinj119_19_2
      Q2.hcardT119_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_19_2 i) (Q2.hfix119_19_2 i) _)
      colCert_119_19_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T119_19
      hfix119_19 hinj119_19 hcardT119_19
      (fun i => conj_mem_of_fixedPoints _ _ (T119_19 i) (hfix119_19 i) _)
      ⟨119, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T119_19_2 Q2.hfix119_19_2 Q2.hinj119_19_2
      Q2.hcardT119_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_19_2 i) (Q2.hfix119_19_2 i) _)
      colCert_119_19_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T119_19
      hfix119_19 hinj119_19 hcardT119_19
      (fun i => conj_mem_of_fixedPoints _ _ (T119_19 i) (hfix119_19 i) _)
      ⟨119, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T119_19_2 Q2.hfix119_19_2 Q2.hinj119_19_2
      Q2.hcardT119_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_19_2 i) (Q2.hfix119_19_2 i) _)
      colCert_119_19_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T119_19
      hfix119_19 hinj119_19 hcardT119_19
      (fun i => conj_mem_of_fixedPoints _ _ (T119_19 i) (hfix119_19 i) _)
      ⟨119, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T119_19_2 Q2.hfix119_19_2 Q2.hinj119_19_2
      Q2.hcardT119_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_19_2 i) (Q2.hfix119_19_2 i) _)
      colCert_119_19_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T119_19
      hfix119_19 hinj119_19 hcardT119_19
      (fun i => conj_mem_of_fixedPoints _ _ (T119_19 i) (hfix119_19 i) _)
      ⟨119, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T119_19_2 Q2.hfix119_19_2 Q2.hinj119_19_2
      Q2.hcardT119_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_19_2 i) (Q2.hfix119_19_2 i) _)
      colCert_119_19_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T119_24
      hfix119_24 hinj119_24 hcardT119_24
      (fun i => conj_mem_of_fixedPoints _ _ (T119_24 i) (hfix119_24 i) _)
      ⟨119, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T119_24_2 Q2.hfix119_24_2 Q2.hinj119_24_2
      Q2.hcardT119_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_24_2 i) (Q2.hfix119_24_2 i) _)
      colCert_119_24_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T119_24
      hfix119_24 hinj119_24 hcardT119_24
      (fun i => conj_mem_of_fixedPoints _ _ (T119_24 i) (hfix119_24 i) _)
      ⟨119, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T119_24_2 Q2.hfix119_24_2 Q2.hinj119_24_2
      Q2.hcardT119_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_24_2 i) (Q2.hfix119_24_2 i) _)
      colCert_119_24_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T119_24
      hfix119_24 hinj119_24 hcardT119_24
      (fun i => conj_mem_of_fixedPoints _ _ (T119_24 i) (hfix119_24 i) _)
      ⟨119, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T119_24_2 Q2.hfix119_24_2 Q2.hinj119_24_2
      Q2.hcardT119_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_24_2 i) (Q2.hfix119_24_2 i) _)
      colCert_119_24_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T119_24
      hfix119_24 hinj119_24 hcardT119_24
      (fun i => conj_mem_of_fixedPoints _ _ (T119_24 i) (hfix119_24 i) _)
      ⟨119, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T119_24_2 Q2.hfix119_24_2 Q2.hinj119_24_2
      Q2.hcardT119_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_24_2 i) (Q2.hfix119_24_2 i) _)
      colCert_119_24_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T119_24
      hfix119_24 hinj119_24 hcardT119_24
      (fun i => conj_mem_of_fixedPoints _ _ (T119_24 i) (hfix119_24 i) _)
      ⟨119, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T119_24_2 Q2.hfix119_24_2 Q2.hinj119_24_2
      Q2.hcardT119_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_24_2 i) (Q2.hfix119_24_2 i) _)
      colCert_119_24_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T119_24
      hfix119_24 hinj119_24 hcardT119_24
      (fun i => conj_mem_of_fixedPoints _ _ (T119_24 i) (hfix119_24 i) _)
      ⟨119, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T119_24_2 Q2.hfix119_24_2 Q2.hinj119_24_2
      Q2.hcardT119_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_24_2 i) (Q2.hfix119_24_2 i) _)
      colCert_119_24_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T119_24
      hfix119_24 hinj119_24 hcardT119_24
      (fun i => conj_mem_of_fixedPoints _ _ (T119_24 i) (hfix119_24 i) _)
      ⟨119, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T119_24_2 Q2.hfix119_24_2 Q2.hinj119_24_2
      Q2.hcardT119_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_24_2 i) (Q2.hfix119_24_2 i) _)
      colCert_119_24_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T119_24
      hfix119_24 hinj119_24 hcardT119_24
      (fun i => conj_mem_of_fixedPoints _ _ (T119_24 i) (hfix119_24 i) _)
      ⟨119, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T119_24_2 Q2.hfix119_24_2 Q2.hinj119_24_2
      Q2.hcardT119_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_24_2 i) (Q2.hfix119_24_2 i) _)
      colCert_119_24_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T119_24
      hfix119_24 hinj119_24 hcardT119_24
      (fun i => conj_mem_of_fixedPoints _ _ (T119_24 i) (hfix119_24 i) _)
      ⟨119, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T119_24_2 Q2.hfix119_24_2 Q2.hinj119_24_2
      Q2.hcardT119_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_24_2 i) (Q2.hfix119_24_2 i) _)
      colCert_119_24_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T119_25
      hfix119_25 hinj119_25 hcardT119_25
      (fun i => conj_mem_of_fixedPoints _ _ (T119_25 i) (hfix119_25 i) _)
      ⟨119, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T119_25_2 Q2.hfix119_25_2 Q2.hinj119_25_2
      Q2.hcardT119_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_25_2 i) (Q2.hfix119_25_2 i) _)
      colCert_119_25_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T119_25
      hfix119_25 hinj119_25 hcardT119_25
      (fun i => conj_mem_of_fixedPoints _ _ (T119_25 i) (hfix119_25 i) _)
      ⟨119, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T119_25_2 Q2.hfix119_25_2 Q2.hinj119_25_2
      Q2.hcardT119_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_25_2 i) (Q2.hfix119_25_2 i) _)
      colCert_119_25_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T119_25
      hfix119_25 hinj119_25 hcardT119_25
      (fun i => conj_mem_of_fixedPoints _ _ (T119_25 i) (hfix119_25 i) _)
      ⟨119, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T119_25_2 Q2.hfix119_25_2 Q2.hinj119_25_2
      Q2.hcardT119_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_25_2 i) (Q2.hfix119_25_2 i) _)
      colCert_119_25_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T119_25
      hfix119_25 hinj119_25 hcardT119_25
      (fun i => conj_mem_of_fixedPoints _ _ (T119_25 i) (hfix119_25 i) _)
      ⟨119, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T119_25_2 Q2.hfix119_25_2 Q2.hinj119_25_2
      Q2.hcardT119_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_25_2 i) (Q2.hfix119_25_2 i) _)
      colCert_119_25_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T119_25
      hfix119_25 hinj119_25 hcardT119_25
      (fun i => conj_mem_of_fixedPoints _ _ (T119_25 i) (hfix119_25 i) _)
      ⟨119, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T119_25_2 Q2.hfix119_25_2 Q2.hinj119_25_2
      Q2.hcardT119_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_25_2 i) (Q2.hfix119_25_2 i) _)
      colCert_119_25_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T119_25
      hfix119_25 hinj119_25 hcardT119_25
      (fun i => conj_mem_of_fixedPoints _ _ (T119_25 i) (hfix119_25 i) _)
      ⟨119, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T119_25_2 Q2.hfix119_25_2 Q2.hinj119_25_2
      Q2.hcardT119_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_25_2 i) (Q2.hfix119_25_2 i) _)
      colCert_119_25_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T119_25
      hfix119_25 hinj119_25 hcardT119_25
      (fun i => conj_mem_of_fixedPoints _ _ (T119_25 i) (hfix119_25 i) _)
      ⟨119, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T119_25_2 Q2.hfix119_25_2 Q2.hinj119_25_2
      Q2.hcardT119_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_25_2 i) (Q2.hfix119_25_2 i) _)
      colCert_119_25_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T119_25
      hfix119_25 hinj119_25 hcardT119_25
      (fun i => conj_mem_of_fixedPoints _ _ (T119_25 i) (hfix119_25 i) _)
      ⟨119, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T119_25_2 Q2.hfix119_25_2 Q2.hinj119_25_2
      Q2.hcardT119_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_25_2 i) (Q2.hfix119_25_2 i) _)
      colCert_119_25_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T119_25
      hfix119_25 hinj119_25 hcardT119_25
      (fun i => conj_mem_of_fixedPoints _ _ (T119_25 i) (hfix119_25 i) _)
      ⟨119, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T119_25_2 Q2.hfix119_25_2 Q2.hinj119_25_2
      Q2.hcardT119_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_25_2 i) (Q2.hfix119_25_2 i) _)
      colCert_119_25_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T119_26
      hfix119_26 hinj119_26 hcardT119_26
      (fun i => conj_mem_of_fixedPoints _ _ (T119_26 i) (hfix119_26 i) _)
      ⟨119, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T119_26_2 Q2.hfix119_26_2 Q2.hinj119_26_2
      Q2.hcardT119_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_26_2 i) (Q2.hfix119_26_2 i) _)
      colCert_119_26_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T119_26
      hfix119_26 hinj119_26 hcardT119_26
      (fun i => conj_mem_of_fixedPoints _ _ (T119_26 i) (hfix119_26 i) _)
      ⟨119, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T119_26_2 Q2.hfix119_26_2 Q2.hinj119_26_2
      Q2.hcardT119_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_26_2 i) (Q2.hfix119_26_2 i) _)
      colCert_119_26_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T119_26
      hfix119_26 hinj119_26 hcardT119_26
      (fun i => conj_mem_of_fixedPoints _ _ (T119_26 i) (hfix119_26 i) _)
      ⟨119, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T119_26_2 Q2.hfix119_26_2 Q2.hinj119_26_2
      Q2.hcardT119_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_26_2 i) (Q2.hfix119_26_2 i) _)
      colCert_119_26_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T119_26
      hfix119_26 hinj119_26 hcardT119_26
      (fun i => conj_mem_of_fixedPoints _ _ (T119_26 i) (hfix119_26 i) _)
      ⟨119, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T119_26_2 Q2.hfix119_26_2 Q2.hinj119_26_2
      Q2.hcardT119_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_26_2 i) (Q2.hfix119_26_2 i) _)
      colCert_119_26_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T119_26
      hfix119_26 hinj119_26 hcardT119_26
      (fun i => conj_mem_of_fixedPoints _ _ (T119_26 i) (hfix119_26 i) _)
      ⟨119, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T119_26_2 Q2.hfix119_26_2 Q2.hinj119_26_2
      Q2.hcardT119_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_26_2 i) (Q2.hfix119_26_2 i) _)
      colCert_119_26_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T119_26
      hfix119_26 hinj119_26 hcardT119_26
      (fun i => conj_mem_of_fixedPoints _ _ (T119_26 i) (hfix119_26 i) _)
      ⟨119, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T119_26_2 Q2.hfix119_26_2 Q2.hinj119_26_2
      Q2.hcardT119_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_26_2 i) (Q2.hfix119_26_2 i) _)
      colCert_119_26_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T119_26
      hfix119_26 hinj119_26 hcardT119_26
      (fun i => conj_mem_of_fixedPoints _ _ (T119_26 i) (hfix119_26 i) _)
      ⟨119, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T119_26_2 Q2.hfix119_26_2 Q2.hinj119_26_2
      Q2.hcardT119_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_26_2 i) (Q2.hfix119_26_2 i) _)
      colCert_119_26_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T119_26
      hfix119_26 hinj119_26 hcardT119_26
      (fun i => conj_mem_of_fixedPoints _ _ (T119_26 i) (hfix119_26 i) _)
      ⟨119, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T119_26_2 Q2.hfix119_26_2 Q2.hinj119_26_2
      Q2.hcardT119_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_26_2 i) (Q2.hfix119_26_2 i) _)
      colCert_119_26_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T119_26
      hfix119_26 hinj119_26 hcardT119_26
      (fun i => conj_mem_of_fixedPoints _ _ (T119_26 i) (hfix119_26 i) _)
      ⟨119, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T119_26_2 Q2.hfix119_26_2 Q2.hinj119_26_2
      Q2.hcardT119_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_26_2 i) (Q2.hfix119_26_2 i) _)
      colCert_119_26_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T119_27
      hfix119_27 hinj119_27 hcardT119_27
      (fun i => conj_mem_of_fixedPoints _ _ (T119_27 i) (hfix119_27 i) _)
      ⟨119, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T119_27_2 Q2.hfix119_27_2 Q2.hinj119_27_2
      Q2.hcardT119_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_27_2 i) (Q2.hfix119_27_2 i) _)
      colCert_119_27_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T119_27
      hfix119_27 hinj119_27 hcardT119_27
      (fun i => conj_mem_of_fixedPoints _ _ (T119_27 i) (hfix119_27 i) _)
      ⟨119, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T119_27_2 Q2.hfix119_27_2 Q2.hinj119_27_2
      Q2.hcardT119_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_27_2 i) (Q2.hfix119_27_2 i) _)
      colCert_119_27_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T119_27
      hfix119_27 hinj119_27 hcardT119_27
      (fun i => conj_mem_of_fixedPoints _ _ (T119_27 i) (hfix119_27 i) _)
      ⟨119, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T119_27_2 Q2.hfix119_27_2 Q2.hinj119_27_2
      Q2.hcardT119_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_27_2 i) (Q2.hfix119_27_2 i) _)
      colCert_119_27_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T119_27
      hfix119_27 hinj119_27 hcardT119_27
      (fun i => conj_mem_of_fixedPoints _ _ (T119_27 i) (hfix119_27 i) _)
      ⟨119, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T119_27_2 Q2.hfix119_27_2 Q2.hinj119_27_2
      Q2.hcardT119_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_27_2 i) (Q2.hfix119_27_2 i) _)
      colCert_119_27_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T119_27
      hfix119_27 hinj119_27 hcardT119_27
      (fun i => conj_mem_of_fixedPoints _ _ (T119_27 i) (hfix119_27 i) _)
      ⟨119, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T119_27_2 Q2.hfix119_27_2 Q2.hinj119_27_2
      Q2.hcardT119_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_27_2 i) (Q2.hfix119_27_2 i) _)
      colCert_119_27_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T119_27
      hfix119_27 hinj119_27 hcardT119_27
      (fun i => conj_mem_of_fixedPoints _ _ (T119_27 i) (hfix119_27 i) _)
      ⟨119, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T119_27_2 Q2.hfix119_27_2 Q2.hinj119_27_2
      Q2.hcardT119_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_27_2 i) (Q2.hfix119_27_2 i) _)
      colCert_119_27_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T119_27
      hfix119_27 hinj119_27 hcardT119_27
      (fun i => conj_mem_of_fixedPoints _ _ (T119_27 i) (hfix119_27 i) _)
      ⟨119, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T119_27_2 Q2.hfix119_27_2 Q2.hinj119_27_2
      Q2.hcardT119_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_27_2 i) (Q2.hfix119_27_2 i) _)
      colCert_119_27_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T119_27
      hfix119_27 hinj119_27 hcardT119_27
      (fun i => conj_mem_of_fixedPoints _ _ (T119_27 i) (hfix119_27 i) _)
      ⟨119, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T119_27_2 Q2.hfix119_27_2 Q2.hinj119_27_2
      Q2.hcardT119_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_27_2 i) (Q2.hfix119_27_2 i) _)
      colCert_119_27_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T119_27
      hfix119_27 hinj119_27 hcardT119_27
      (fun i => conj_mem_of_fixedPoints _ _ (T119_27 i) (hfix119_27 i) _)
      ⟨119, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T119_27_2 Q2.hfix119_27_2 Q2.hinj119_27_2
      Q2.hcardT119_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_27_2 i) (Q2.hfix119_27_2 i) _)
      colCert_119_27_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_31_0 (hp : 0 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 0 (transLenTr ⟨31, by decide⟩ 0 hp)) T119_31
      hfix119_31 hinj119_31 hcardT119_31
      (fun i => conj_mem_of_fixedPoints _ _ (T119_31 i) (hfix119_31 i) _)
      ⟨119, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 0 hp) Q2.T119_31_2 Q2.hfix119_31_2 Q2.hinj119_31_2
      Q2.hcardT119_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_31_2 i) (Q2.hfix119_31_2 i) _)
      colCert_119_31_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_31_1 (hp : 1 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 1 (transLenTr ⟨31, by decide⟩ 1 hp)) T119_31
      hfix119_31 hinj119_31 hcardT119_31
      (fun i => conj_mem_of_fixedPoints _ _ (T119_31 i) (hfix119_31 i) _)
      ⟨119, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 1 hp) Q2.T119_31_2 Q2.hfix119_31_2 Q2.hinj119_31_2
      Q2.hcardT119_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_31_2 i) (Q2.hfix119_31_2 i) _)
      colCert_119_31_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_31_2 (hp : 2 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 2 (transLenTr ⟨31, by decide⟩ 2 hp)) T119_31
      hfix119_31 hinj119_31 hcardT119_31
      (fun i => conj_mem_of_fixedPoints _ _ (T119_31 i) (hfix119_31 i) _)
      ⟨119, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 2 hp) Q2.T119_31_2 Q2.hfix119_31_2 Q2.hinj119_31_2
      Q2.hcardT119_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_31_2 i) (Q2.hfix119_31_2 i) _)
      colCert_119_31_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_31_3 (hp : 3 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 3 (transLenTr ⟨31, by decide⟩ 3 hp)) T119_31
      hfix119_31 hinj119_31 hcardT119_31
      (fun i => conj_mem_of_fixedPoints _ _ (T119_31 i) (hfix119_31 i) _)
      ⟨119, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 3 hp) Q2.T119_31_2 Q2.hfix119_31_2 Q2.hinj119_31_2
      Q2.hcardT119_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_31_2 i) (Q2.hfix119_31_2 i) _)
      colCert_119_31_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_31_4 (hp : 4 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 4 (transLenTr ⟨31, by decide⟩ 4 hp)) T119_31
      hfix119_31 hinj119_31 hcardT119_31
      (fun i => conj_mem_of_fixedPoints _ _ (T119_31 i) (hfix119_31 i) _)
      ⟨119, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 4 hp) Q2.T119_31_2 Q2.hfix119_31_2 Q2.hinj119_31_2
      Q2.hcardT119_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_31_2 i) (Q2.hfix119_31_2 i) _)
      colCert_119_31_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_31_5 (hp : 5 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp)) T119_31
      hfix119_31 hinj119_31 hcardT119_31
      (fun i => conj_mem_of_fixedPoints _ _ (T119_31 i) (hfix119_31 i) _)
      ⟨119, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 5 hp) Q2.T119_31_2 Q2.hfix119_31_2 Q2.hinj119_31_2
      Q2.hcardT119_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_31_2 i) (Q2.hfix119_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 5 (transLenTr ⟨31, by decide⟩ 5 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T119_31 = colFn colCertDiv_119_31_5.D1 (m := 5) from colCertDiv_119_31_5.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 5 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T119_31_2 = colFn colCertDiv_119_31_5.D2 (m := 5) from colCertDiv_119_31_5.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_31_5_match


theorem leaf_119_31_10 (hp : 10 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp)) T119_31
      hfix119_31 hinj119_31 hcardT119_31
      (fun i => conj_mem_of_fixedPoints _ _ (T119_31 i) (hfix119_31 i) _)
      ⟨119, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 10 hp) Q2.T119_31_2 Q2.hfix119_31_2 Q2.hinj119_31_2
      Q2.hcardT119_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_31_2 i) (Q2.hfix119_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 10 (transLenTr ⟨31, by decide⟩ 10 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T119_31 = colFn colCertDiv_119_31_10.D1 (m := 5) from colCertDiv_119_31_10.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 10 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T119_31_2 = colFn colCertDiv_119_31_10.D2 (m := 5) from colCertDiv_119_31_10.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_31_10_match


theorem leaf_119_31_15 (hp : 15 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp)) T119_31
      hfix119_31 hinj119_31 hcardT119_31
      (fun i => conj_mem_of_fixedPoints _ _ (T119_31 i) (hfix119_31 i) _)
      ⟨119, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 15 hp) Q2.T119_31_2 Q2.hfix119_31_2 Q2.hinj119_31_2
      Q2.hcardT119_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_31_2 i) (Q2.hfix119_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 15 (transLenTr ⟨31, by decide⟩ 15 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T119_31 = colFn colCertDiv_119_31_15.D1 (m := 5) from colCertDiv_119_31_15.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 15 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T119_31_2 = colFn colCertDiv_119_31_15.D2 (m := 5) from colCertDiv_119_31_15.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_31_15_match


theorem leaf_119_31_20 (hp : 20 < (Q2.transData.getD 31 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨31, by decide⟩ : Fin 148)) (colE2 ⟨31, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨31, by decide⟩ : Fin 148))
        (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨31, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp)) T119_31
      hfix119_31 hinj119_31 hcardT119_31
      (fun i => conj_mem_of_fixedPoints _ _ (T119_31 i) (hfix119_31 i) _)
      ⟨119, by decide⟩ ⟨31, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨31, by decide⟩ 20 hp) Q2.T119_31_2 Q2.hfix119_31_2 Q2.hinj119_31_2
      Q2.hcardT119_31_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_31_2 i) (Q2.hfix119_31_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨31, by decide⟩ 20 (transLenTr ⟨31, by decide⟩ 20 hp) : ↥(reps ⟨31, by decide⟩)) : Coordinate 1)
        T119_31 = colFn colCertDiv_119_31_20.D1 (m := 5) from colCertDiv_119_31_20.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨31, by decide⟩ 20 hp : ↥(Q2.reps ⟨31, by decide⟩)) : Coordinate 2)
        Q2.T119_31_2 = colFn colCertDiv_119_31_20.D2 (m := 5) from colCertDiv_119_31_20.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_31_20_match


theorem leaf_119_36_0 (hp : 0 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 0 (transLenTr ⟨36, by decide⟩ 0 hp)) T119_36
      hfix119_36 hinj119_36 hcardT119_36
      (fun i => conj_mem_of_fixedPoints _ _ (T119_36 i) (hfix119_36 i) _)
      ⟨119, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 0 hp) Q2.T119_36_2 Q2.hfix119_36_2 Q2.hinj119_36_2
      Q2.hcardT119_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_36_2 i) (Q2.hfix119_36_2 i) _)
      colCert_119_36_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_36_1 (hp : 1 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 1 (transLenTr ⟨36, by decide⟩ 1 hp)) T119_36
      hfix119_36 hinj119_36 hcardT119_36
      (fun i => conj_mem_of_fixedPoints _ _ (T119_36 i) (hfix119_36 i) _)
      ⟨119, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 1 hp) Q2.T119_36_2 Q2.hfix119_36_2 Q2.hinj119_36_2
      Q2.hcardT119_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_36_2 i) (Q2.hfix119_36_2 i) _)
      colCert_119_36_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_36_2 (hp : 2 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 2 (transLenTr ⟨36, by decide⟩ 2 hp)) T119_36
      hfix119_36 hinj119_36 hcardT119_36
      (fun i => conj_mem_of_fixedPoints _ _ (T119_36 i) (hfix119_36 i) _)
      ⟨119, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 2 hp) Q2.T119_36_2 Q2.hfix119_36_2 Q2.hinj119_36_2
      Q2.hcardT119_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_36_2 i) (Q2.hfix119_36_2 i) _)
      colCert_119_36_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_36_3 (hp : 3 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 3 (transLenTr ⟨36, by decide⟩ 3 hp)) T119_36
      hfix119_36 hinj119_36 hcardT119_36
      (fun i => conj_mem_of_fixedPoints _ _ (T119_36 i) (hfix119_36 i) _)
      ⟨119, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 3 hp) Q2.T119_36_2 Q2.hfix119_36_2 Q2.hinj119_36_2
      Q2.hcardT119_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_36_2 i) (Q2.hfix119_36_2 i) _)
      colCert_119_36_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_36_4 (hp : 4 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 4 (transLenTr ⟨36, by decide⟩ 4 hp)) T119_36
      hfix119_36 hinj119_36 hcardT119_36
      (fun i => conj_mem_of_fixedPoints _ _ (T119_36 i) (hfix119_36 i) _)
      ⟨119, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 4 hp) Q2.T119_36_2 Q2.hfix119_36_2 Q2.hinj119_36_2
      Q2.hcardT119_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_36_2 i) (Q2.hfix119_36_2 i) _)
      colCert_119_36_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_36_5 (hp : 5 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp)) T119_36
      hfix119_36 hinj119_36 hcardT119_36
      (fun i => conj_mem_of_fixedPoints _ _ (T119_36 i) (hfix119_36 i) _)
      ⟨119, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 5 hp) Q2.T119_36_2 Q2.hfix119_36_2 Q2.hinj119_36_2
      Q2.hcardT119_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_36_2 i) (Q2.hfix119_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 5 (transLenTr ⟨36, by decide⟩ 5 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T119_36 = colFn colCertDiv_119_36_5.D1 (m := 5) from colCertDiv_119_36_5.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 5 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T119_36_2 = colFn colCertDiv_119_36_5.D2 (m := 5) from colCertDiv_119_36_5.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_36_5_match


theorem leaf_119_36_10 (hp : 10 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp)) T119_36
      hfix119_36 hinj119_36 hcardT119_36
      (fun i => conj_mem_of_fixedPoints _ _ (T119_36 i) (hfix119_36 i) _)
      ⟨119, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 10 hp) Q2.T119_36_2 Q2.hfix119_36_2 Q2.hinj119_36_2
      Q2.hcardT119_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_36_2 i) (Q2.hfix119_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 10 (transLenTr ⟨36, by decide⟩ 10 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T119_36 = colFn colCertDiv_119_36_10.D1 (m := 5) from colCertDiv_119_36_10.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 10 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T119_36_2 = colFn colCertDiv_119_36_10.D2 (m := 5) from colCertDiv_119_36_10.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_36_10_match


theorem leaf_119_36_15 (hp : 15 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp)) T119_36
      hfix119_36 hinj119_36 hcardT119_36
      (fun i => conj_mem_of_fixedPoints _ _ (T119_36 i) (hfix119_36 i) _)
      ⟨119, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 15 hp) Q2.T119_36_2 Q2.hfix119_36_2 Q2.hinj119_36_2
      Q2.hcardT119_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_36_2 i) (Q2.hfix119_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 15 (transLenTr ⟨36, by decide⟩ 15 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T119_36 = colFn colCertDiv_119_36_15.D1 (m := 5) from colCertDiv_119_36_15.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 15 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T119_36_2 = colFn colCertDiv_119_36_15.D2 (m := 5) from colCertDiv_119_36_15.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_36_15_match


theorem leaf_119_36_20 (hp : 20 < (Q2.transData.getD 36 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨36, by decide⟩ : Fin 148)) (colE2 ⟨36, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨36, by decide⟩ : Fin 148))
        (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨36, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp)) T119_36
      hfix119_36 hinj119_36 hcardT119_36
      (fun i => conj_mem_of_fixedPoints _ _ (T119_36 i) (hfix119_36 i) _)
      ⟨119, by decide⟩ ⟨36, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨36, by decide⟩ 20 hp) Q2.T119_36_2 Q2.hfix119_36_2 Q2.hinj119_36_2
      Q2.hcardT119_36_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_36_2 i) (Q2.hfix119_36_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨36, by decide⟩ 20 (transLenTr ⟨36, by decide⟩ 20 hp) : ↥(reps ⟨36, by decide⟩)) : Coordinate 1)
        T119_36 = colFn colCertDiv_119_36_20.D1 (m := 5) from colCertDiv_119_36_20.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨36, by decide⟩ 20 hp : ↥(Q2.reps ⟨36, by decide⟩)) : Coordinate 2)
        Q2.T119_36_2 = colFn colCertDiv_119_36_20.D2 (m := 5) from colCertDiv_119_36_20.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_36_20_match


theorem leaf_119_41_0 (hp : 0 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 0 (transLenTr ⟨41, by decide⟩ 0 hp)) T119_41
      hfix119_41 hinj119_41 hcardT119_41
      (fun i => conj_mem_of_fixedPoints _ _ (T119_41 i) (hfix119_41 i) _)
      ⟨119, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 0 hp) Q2.T119_41_2 Q2.hfix119_41_2 Q2.hinj119_41_2
      Q2.hcardT119_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_41_2 i) (Q2.hfix119_41_2 i) _)
      colCert_119_41_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_41_1 (hp : 1 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 1 (transLenTr ⟨41, by decide⟩ 1 hp)) T119_41
      hfix119_41 hinj119_41 hcardT119_41
      (fun i => conj_mem_of_fixedPoints _ _ (T119_41 i) (hfix119_41 i) _)
      ⟨119, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 1 hp) Q2.T119_41_2 Q2.hfix119_41_2 Q2.hinj119_41_2
      Q2.hcardT119_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_41_2 i) (Q2.hfix119_41_2 i) _)
      colCert_119_41_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_41_2 (hp : 2 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 2 (transLenTr ⟨41, by decide⟩ 2 hp)) T119_41
      hfix119_41 hinj119_41 hcardT119_41
      (fun i => conj_mem_of_fixedPoints _ _ (T119_41 i) (hfix119_41 i) _)
      ⟨119, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 2 hp) Q2.T119_41_2 Q2.hfix119_41_2 Q2.hinj119_41_2
      Q2.hcardT119_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_41_2 i) (Q2.hfix119_41_2 i) _)
      colCert_119_41_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_41_3 (hp : 3 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 3 (transLenTr ⟨41, by decide⟩ 3 hp)) T119_41
      hfix119_41 hinj119_41 hcardT119_41
      (fun i => conj_mem_of_fixedPoints _ _ (T119_41 i) (hfix119_41 i) _)
      ⟨119, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 3 hp) Q2.T119_41_2 Q2.hfix119_41_2 Q2.hinj119_41_2
      Q2.hcardT119_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_41_2 i) (Q2.hfix119_41_2 i) _)
      colCert_119_41_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_41_4 (hp : 4 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 4 (transLenTr ⟨41, by decide⟩ 4 hp)) T119_41
      hfix119_41 hinj119_41 hcardT119_41
      (fun i => conj_mem_of_fixedPoints _ _ (T119_41 i) (hfix119_41 i) _)
      ⟨119, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 4 hp) Q2.T119_41_2 Q2.hfix119_41_2 Q2.hinj119_41_2
      Q2.hcardT119_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_41_2 i) (Q2.hfix119_41_2 i) _)
      colCert_119_41_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_41_5 (hp : 5 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp)) T119_41
      hfix119_41 hinj119_41 hcardT119_41
      (fun i => conj_mem_of_fixedPoints _ _ (T119_41 i) (hfix119_41 i) _)
      ⟨119, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 5 hp) Q2.T119_41_2 Q2.hfix119_41_2 Q2.hinj119_41_2
      Q2.hcardT119_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_41_2 i) (Q2.hfix119_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 5 (transLenTr ⟨41, by decide⟩ 5 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T119_41 = colFn colCertDiv_119_41_5.D1 (m := 5) from colCertDiv_119_41_5.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 5 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T119_41_2 = colFn colCertDiv_119_41_5.D2 (m := 5) from colCertDiv_119_41_5.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_41_5_match


theorem leaf_119_41_10 (hp : 10 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp)) T119_41
      hfix119_41 hinj119_41 hcardT119_41
      (fun i => conj_mem_of_fixedPoints _ _ (T119_41 i) (hfix119_41 i) _)
      ⟨119, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 10 hp) Q2.T119_41_2 Q2.hfix119_41_2 Q2.hinj119_41_2
      Q2.hcardT119_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_41_2 i) (Q2.hfix119_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 10 (transLenTr ⟨41, by decide⟩ 10 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T119_41 = colFn colCertDiv_119_41_10.D1 (m := 5) from colCertDiv_119_41_10.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 10 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T119_41_2 = colFn colCertDiv_119_41_10.D2 (m := 5) from colCertDiv_119_41_10.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_41_10_match


theorem leaf_119_41_15 (hp : 15 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp)) T119_41
      hfix119_41 hinj119_41 hcardT119_41
      (fun i => conj_mem_of_fixedPoints _ _ (T119_41 i) (hfix119_41 i) _)
      ⟨119, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 15 hp) Q2.T119_41_2 Q2.hfix119_41_2 Q2.hinj119_41_2
      Q2.hcardT119_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_41_2 i) (Q2.hfix119_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 15 (transLenTr ⟨41, by decide⟩ 15 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T119_41 = colFn colCertDiv_119_41_15.D1 (m := 5) from colCertDiv_119_41_15.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 15 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T119_41_2 = colFn colCertDiv_119_41_15.D2 (m := 5) from colCertDiv_119_41_15.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_41_15_match


theorem leaf_119_41_20 (hp : 20 < (Q2.transData.getD 41 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨41, by decide⟩ : Fin 148)) (colE2 ⟨41, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨41, by decide⟩ : Fin 148))
        (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨41, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp)) T119_41
      hfix119_41 hinj119_41 hcardT119_41
      (fun i => conj_mem_of_fixedPoints _ _ (T119_41 i) (hfix119_41 i) _)
      ⟨119, by decide⟩ ⟨41, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨41, by decide⟩ 20 hp) Q2.T119_41_2 Q2.hfix119_41_2 Q2.hinj119_41_2
      Q2.hcardT119_41_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_41_2 i) (Q2.hfix119_41_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨41, by decide⟩ 20 (transLenTr ⟨41, by decide⟩ 20 hp) : ↥(reps ⟨41, by decide⟩)) : Coordinate 1)
        T119_41 = colFn colCertDiv_119_41_20.D1 (m := 5) from colCertDiv_119_41_20.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨41, by decide⟩ 20 hp : ↥(Q2.reps ⟨41, by decide⟩)) : Coordinate 2)
        Q2.T119_41_2 = colFn colCertDiv_119_41_20.D2 (m := 5) from colCertDiv_119_41_20.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_41_20_match


theorem leaf_119_46_0 (hp : 0 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 0 (transLenTr ⟨46, by decide⟩ 0 hp)) T119_46
      hfix119_46 hinj119_46 hcardT119_46
      (fun i => conj_mem_of_fixedPoints _ _ (T119_46 i) (hfix119_46 i) _)
      ⟨119, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 0 hp) Q2.T119_46_2 Q2.hfix119_46_2 Q2.hinj119_46_2
      Q2.hcardT119_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_46_2 i) (Q2.hfix119_46_2 i) _)
      colCert_119_46_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_46_1 (hp : 1 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 1 (transLenTr ⟨46, by decide⟩ 1 hp)) T119_46
      hfix119_46 hinj119_46 hcardT119_46
      (fun i => conj_mem_of_fixedPoints _ _ (T119_46 i) (hfix119_46 i) _)
      ⟨119, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 1 hp) Q2.T119_46_2 Q2.hfix119_46_2 Q2.hinj119_46_2
      Q2.hcardT119_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_46_2 i) (Q2.hfix119_46_2 i) _)
      colCert_119_46_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_46_2 (hp : 2 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 2 (transLenTr ⟨46, by decide⟩ 2 hp)) T119_46
      hfix119_46 hinj119_46 hcardT119_46
      (fun i => conj_mem_of_fixedPoints _ _ (T119_46 i) (hfix119_46 i) _)
      ⟨119, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 2 hp) Q2.T119_46_2 Q2.hfix119_46_2 Q2.hinj119_46_2
      Q2.hcardT119_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_46_2 i) (Q2.hfix119_46_2 i) _)
      colCert_119_46_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_46_3 (hp : 3 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 3 (transLenTr ⟨46, by decide⟩ 3 hp)) T119_46
      hfix119_46 hinj119_46 hcardT119_46
      (fun i => conj_mem_of_fixedPoints _ _ (T119_46 i) (hfix119_46 i) _)
      ⟨119, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 3 hp) Q2.T119_46_2 Q2.hfix119_46_2 Q2.hinj119_46_2
      Q2.hcardT119_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_46_2 i) (Q2.hfix119_46_2 i) _)
      colCert_119_46_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_46_4 (hp : 4 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 4 (transLenTr ⟨46, by decide⟩ 4 hp)) T119_46
      hfix119_46 hinj119_46 hcardT119_46
      (fun i => conj_mem_of_fixedPoints _ _ (T119_46 i) (hfix119_46 i) _)
      ⟨119, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 4 hp) Q2.T119_46_2 Q2.hfix119_46_2 Q2.hinj119_46_2
      Q2.hcardT119_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_46_2 i) (Q2.hfix119_46_2 i) _)
      colCert_119_46_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_46_5 (hp : 5 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp)) T119_46
      hfix119_46 hinj119_46 hcardT119_46
      (fun i => conj_mem_of_fixedPoints _ _ (T119_46 i) (hfix119_46 i) _)
      ⟨119, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 5 hp) Q2.T119_46_2 Q2.hfix119_46_2 Q2.hinj119_46_2
      Q2.hcardT119_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_46_2 i) (Q2.hfix119_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 5 (transLenTr ⟨46, by decide⟩ 5 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T119_46 = colFn colCertDiv_119_46_5.D1 (m := 5) from colCertDiv_119_46_5.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 5 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T119_46_2 = colFn colCertDiv_119_46_5.D2 (m := 5) from colCertDiv_119_46_5.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_46_5_match


theorem leaf_119_46_10 (hp : 10 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp)) T119_46
      hfix119_46 hinj119_46 hcardT119_46
      (fun i => conj_mem_of_fixedPoints _ _ (T119_46 i) (hfix119_46 i) _)
      ⟨119, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 10 hp) Q2.T119_46_2 Q2.hfix119_46_2 Q2.hinj119_46_2
      Q2.hcardT119_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_46_2 i) (Q2.hfix119_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 10 (transLenTr ⟨46, by decide⟩ 10 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T119_46 = colFn colCertDiv_119_46_10.D1 (m := 5) from colCertDiv_119_46_10.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 10 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T119_46_2 = colFn colCertDiv_119_46_10.D2 (m := 5) from colCertDiv_119_46_10.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_46_10_match


theorem leaf_119_46_15 (hp : 15 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp)) T119_46
      hfix119_46 hinj119_46 hcardT119_46
      (fun i => conj_mem_of_fixedPoints _ _ (T119_46 i) (hfix119_46 i) _)
      ⟨119, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 15 hp) Q2.T119_46_2 Q2.hfix119_46_2 Q2.hinj119_46_2
      Q2.hcardT119_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_46_2 i) (Q2.hfix119_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 15 (transLenTr ⟨46, by decide⟩ 15 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T119_46 = colFn colCertDiv_119_46_15.D1 (m := 5) from colCertDiv_119_46_15.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 15 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T119_46_2 = colFn colCertDiv_119_46_15.D2 (m := 5) from colCertDiv_119_46_15.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_46_15_match


theorem leaf_119_46_20 (hp : 20 < (Q2.transData.getD 46 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨46, by decide⟩ : Fin 148)) (colE2 ⟨46, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨46, by decide⟩ : Fin 148))
        (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨46, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp)) T119_46
      hfix119_46 hinj119_46 hcardT119_46
      (fun i => conj_mem_of_fixedPoints _ _ (T119_46 i) (hfix119_46 i) _)
      ⟨119, by decide⟩ ⟨46, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨46, by decide⟩ 20 hp) Q2.T119_46_2 Q2.hfix119_46_2 Q2.hinj119_46_2
      Q2.hcardT119_46_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_46_2 i) (Q2.hfix119_46_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨46, by decide⟩ 20 (transLenTr ⟨46, by decide⟩ 20 hp) : ↥(reps ⟨46, by decide⟩)) : Coordinate 1)
        T119_46 = colFn colCertDiv_119_46_20.D1 (m := 5) from colCertDiv_119_46_20.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨46, by decide⟩ 20 hp : ↥(Q2.reps ⟨46, by decide⟩)) : Coordinate 2)
        Q2.T119_46_2 = colFn colCertDiv_119_46_20.D2 (m := 5) from colCertDiv_119_46_20.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_46_20_match


theorem leaf_119_51_0 (hp : 0 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 0 (transLenTr ⟨51, by decide⟩ 0 hp)) T119_51
      hfix119_51 hinj119_51 hcardT119_51
      (fun i => conj_mem_of_fixedPoints _ _ (T119_51 i) (hfix119_51 i) _)
      ⟨119, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 0 hp) Q2.T119_51_2 Q2.hfix119_51_2 Q2.hinj119_51_2
      Q2.hcardT119_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_51_2 i) (Q2.hfix119_51_2 i) _)
      colCert_119_51_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_51_1 (hp : 1 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 1 (transLenTr ⟨51, by decide⟩ 1 hp)) T119_51
      hfix119_51 hinj119_51 hcardT119_51
      (fun i => conj_mem_of_fixedPoints _ _ (T119_51 i) (hfix119_51 i) _)
      ⟨119, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 1 hp) Q2.T119_51_2 Q2.hfix119_51_2 Q2.hinj119_51_2
      Q2.hcardT119_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_51_2 i) (Q2.hfix119_51_2 i) _)
      colCert_119_51_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_51_2 (hp : 2 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 2 (transLenTr ⟨51, by decide⟩ 2 hp)) T119_51
      hfix119_51 hinj119_51 hcardT119_51
      (fun i => conj_mem_of_fixedPoints _ _ (T119_51 i) (hfix119_51 i) _)
      ⟨119, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 2 hp) Q2.T119_51_2 Q2.hfix119_51_2 Q2.hinj119_51_2
      Q2.hcardT119_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_51_2 i) (Q2.hfix119_51_2 i) _)
      colCert_119_51_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_51_3 (hp : 3 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 3 (transLenTr ⟨51, by decide⟩ 3 hp)) T119_51
      hfix119_51 hinj119_51 hcardT119_51
      (fun i => conj_mem_of_fixedPoints _ _ (T119_51 i) (hfix119_51 i) _)
      ⟨119, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 3 hp) Q2.T119_51_2 Q2.hfix119_51_2 Q2.hinj119_51_2
      Q2.hcardT119_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_51_2 i) (Q2.hfix119_51_2 i) _)
      colCert_119_51_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_51_4 (hp : 4 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 4 (transLenTr ⟨51, by decide⟩ 4 hp)) T119_51
      hfix119_51 hinj119_51 hcardT119_51
      (fun i => conj_mem_of_fixedPoints _ _ (T119_51 i) (hfix119_51 i) _)
      ⟨119, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 4 hp) Q2.T119_51_2 Q2.hfix119_51_2 Q2.hinj119_51_2
      Q2.hcardT119_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_51_2 i) (Q2.hfix119_51_2 i) _)
      colCert_119_51_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_51_5 (hp : 5 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp)) T119_51
      hfix119_51 hinj119_51 hcardT119_51
      (fun i => conj_mem_of_fixedPoints _ _ (T119_51 i) (hfix119_51 i) _)
      ⟨119, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 5 hp) Q2.T119_51_2 Q2.hfix119_51_2 Q2.hinj119_51_2
      Q2.hcardT119_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_51_2 i) (Q2.hfix119_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 5 (transLenTr ⟨51, by decide⟩ 5 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T119_51 = colFn colCertDiv_119_51_5.D1 (m := 5) from colCertDiv_119_51_5.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 5 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T119_51_2 = colFn colCertDiv_119_51_5.D2 (m := 5) from colCertDiv_119_51_5.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_51_5_match


theorem leaf_119_51_10 (hp : 10 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp)) T119_51
      hfix119_51 hinj119_51 hcardT119_51
      (fun i => conj_mem_of_fixedPoints _ _ (T119_51 i) (hfix119_51 i) _)
      ⟨119, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 10 hp) Q2.T119_51_2 Q2.hfix119_51_2 Q2.hinj119_51_2
      Q2.hcardT119_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_51_2 i) (Q2.hfix119_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 10 (transLenTr ⟨51, by decide⟩ 10 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T119_51 = colFn colCertDiv_119_51_10.D1 (m := 5) from colCertDiv_119_51_10.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 10 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T119_51_2 = colFn colCertDiv_119_51_10.D2 (m := 5) from colCertDiv_119_51_10.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_51_10_match


theorem leaf_119_51_15 (hp : 15 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp)) T119_51
      hfix119_51 hinj119_51 hcardT119_51
      (fun i => conj_mem_of_fixedPoints _ _ (T119_51 i) (hfix119_51 i) _)
      ⟨119, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 15 hp) Q2.T119_51_2 Q2.hfix119_51_2 Q2.hinj119_51_2
      Q2.hcardT119_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_51_2 i) (Q2.hfix119_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 15 (transLenTr ⟨51, by decide⟩ 15 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T119_51 = colFn colCertDiv_119_51_15.D1 (m := 5) from colCertDiv_119_51_15.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 15 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T119_51_2 = colFn colCertDiv_119_51_15.D2 (m := 5) from colCertDiv_119_51_15.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_51_15_match


theorem leaf_119_51_20 (hp : 20 < (Q2.transData.getD 51 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨51, by decide⟩ : Fin 148)) (colE2 ⟨51, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨51, by decide⟩ : Fin 148))
        (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨51, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp)) T119_51
      hfix119_51 hinj119_51 hcardT119_51
      (fun i => conj_mem_of_fixedPoints _ _ (T119_51 i) (hfix119_51 i) _)
      ⟨119, by decide⟩ ⟨51, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨51, by decide⟩ 20 hp) Q2.T119_51_2 Q2.hfix119_51_2 Q2.hinj119_51_2
      Q2.hcardT119_51_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_51_2 i) (Q2.hfix119_51_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨51, by decide⟩ 20 (transLenTr ⟨51, by decide⟩ 20 hp) : ↥(reps ⟨51, by decide⟩)) : Coordinate 1)
        T119_51 = colFn colCertDiv_119_51_20.D1 (m := 5) from colCertDiv_119_51_20.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨51, by decide⟩ 20 hp : ↥(Q2.reps ⟨51, by decide⟩)) : Coordinate 2)
        Q2.T119_51_2 = colFn colCertDiv_119_51_20.D2 (m := 5) from colCertDiv_119_51_20.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_51_20_match


theorem leaf_119_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T119_53
      hfix119_53 hinj119_53 hcardT119_53
      (fun i => conj_mem_of_fixedPoints _ _ (T119_53 i) (hfix119_53 i) _)
      ⟨119, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T119_53_2 Q2.hfix119_53_2 Q2.hinj119_53_2
      Q2.hcardT119_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_53_2 i) (Q2.hfix119_53_2 i) _)
      colCert_119_53_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T119_53
      hfix119_53 hinj119_53 hcardT119_53
      (fun i => conj_mem_of_fixedPoints _ _ (T119_53 i) (hfix119_53 i) _)
      ⟨119, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T119_53_2 Q2.hfix119_53_2 Q2.hinj119_53_2
      Q2.hcardT119_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_53_2 i) (Q2.hfix119_53_2 i) _)
      colCert_119_53_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T119_53
      hfix119_53 hinj119_53 hcardT119_53
      (fun i => conj_mem_of_fixedPoints _ _ (T119_53 i) (hfix119_53 i) _)
      ⟨119, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T119_53_2 Q2.hfix119_53_2 Q2.hinj119_53_2
      Q2.hcardT119_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_53_2 i) (Q2.hfix119_53_2 i) _)
      colCert_119_53_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T119_53
      hfix119_53 hinj119_53 hcardT119_53
      (fun i => conj_mem_of_fixedPoints _ _ (T119_53 i) (hfix119_53 i) _)
      ⟨119, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T119_53_2 Q2.hfix119_53_2 Q2.hinj119_53_2
      Q2.hcardT119_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_53_2 i) (Q2.hfix119_53_2 i) _)
      colCert_119_53_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T119_53
      hfix119_53 hinj119_53 hcardT119_53
      (fun i => conj_mem_of_fixedPoints _ _ (T119_53 i) (hfix119_53 i) _)
      ⟨119, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T119_53_2 Q2.hfix119_53_2 Q2.hinj119_53_2
      Q2.hcardT119_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_53_2 i) (Q2.hfix119_53_2 i) _)
      colCert_119_53_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T119_53
      hfix119_53 hinj119_53 hcardT119_53
      (fun i => conj_mem_of_fixedPoints _ _ (T119_53 i) (hfix119_53 i) _)
      ⟨119, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T119_53_2 Q2.hfix119_53_2 Q2.hinj119_53_2
      Q2.hcardT119_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_53_2 i) (Q2.hfix119_53_2 i) _)
      colCert_119_53_5.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T119_53
      hfix119_53 hinj119_53 hcardT119_53
      (fun i => conj_mem_of_fixedPoints _ _ (T119_53 i) (hfix119_53 i) _)
      ⟨119, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T119_53_2 Q2.hfix119_53_2 Q2.hinj119_53_2
      Q2.hcardT119_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_53_2 i) (Q2.hfix119_53_2 i) _)
      colCert_119_53_10.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T119_53
      hfix119_53 hinj119_53 hcardT119_53
      (fun i => conj_mem_of_fixedPoints _ _ (T119_53 i) (hfix119_53 i) _)
      ⟨119, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T119_53_2 Q2.hfix119_53_2 Q2.hinj119_53_2
      Q2.hcardT119_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_53_2 i) (Q2.hfix119_53_2 i) _)
      colCert_119_53_15.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T119_53
      hfix119_53 hinj119_53 hcardT119_53
      (fun i => conj_mem_of_fixedPoints _ _ (T119_53 i) (hfix119_53 i) _)
      ⟨119, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T119_53_2 Q2.hfix119_53_2 Q2.hinj119_53_2
      Q2.hcardT119_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_53_2 i) (Q2.hfix119_53_2 i) _)
      colCert_119_53_20.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_70_0 (hp : 0 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 0 (transLenTr ⟨70, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 0 (transLenTr ⟨70, by decide⟩ 0 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 0 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      colCert_119_70_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_70_1 (hp : 1 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 1 (transLenTr ⟨70, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 1 (transLenTr ⟨70, by decide⟩ 1 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 1 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      colCert_119_70_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_70_2 (hp : 2 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 2 (transLenTr ⟨70, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 2 (transLenTr ⟨70, by decide⟩ 2 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 2 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      colCert_119_70_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_70_3 (hp : 3 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 3 (transLenTr ⟨70, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 3 (transLenTr ⟨70, by decide⟩ 3 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 3 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      colCert_119_70_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_70_4 (hp : 4 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 4 (transLenTr ⟨70, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 4 (transLenTr ⟨70, by decide⟩ 4 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 4 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      colCert_119_70_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_70_5 (hp : 5 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 5 (transLenTr ⟨70, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 5 (transLenTr ⟨70, by decide⟩ 5 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 5 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 5 (transLenTr ⟨70, by decide⟩ 5 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_5.D1 (m := 5) from colCertDiv_119_70_5.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 5 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_5.D2 (m := 5) from colCertDiv_119_70_5.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_5_match


theorem leaf_119_70_6 (hp : 6 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 6 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 6 (transLenTr ⟨70, by decide⟩ 6 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 6 (transLenTr ⟨70, by decide⟩ 6 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 6 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 6 (transLenTr ⟨70, by decide⟩ 6 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_6.D1 (m := 5) from colCertDiv_119_70_6.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 6 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_6.D2 (m := 5) from colCertDiv_119_70_6.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_6_match


theorem leaf_119_70_7 (hp : 7 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 7 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 7 (transLenTr ⟨70, by decide⟩ 7 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 7 (transLenTr ⟨70, by decide⟩ 7 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 7 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 7 (transLenTr ⟨70, by decide⟩ 7 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_7.D1 (m := 5) from colCertDiv_119_70_7.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 7 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_7.D2 (m := 5) from colCertDiv_119_70_7.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_7_match


theorem leaf_119_70_8 (hp : 8 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 8 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 8 (transLenTr ⟨70, by decide⟩ 8 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 8 (transLenTr ⟨70, by decide⟩ 8 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 8 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 8 (transLenTr ⟨70, by decide⟩ 8 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_8.D1 (m := 5) from colCertDiv_119_70_8.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 8 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_8.D2 (m := 5) from colCertDiv_119_70_8.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_8_match


theorem leaf_119_70_9 (hp : 9 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 9 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 9 (transLenTr ⟨70, by decide⟩ 9 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 9 (transLenTr ⟨70, by decide⟩ 9 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 9 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 9 (transLenTr ⟨70, by decide⟩ 9 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_9.D1 (m := 5) from colCertDiv_119_70_9.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 9 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_9.D2 (m := 5) from colCertDiv_119_70_9.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_9_match


theorem leaf_119_70_10 (hp : 10 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 10 (transLenTr ⟨70, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 10 (transLenTr ⟨70, by decide⟩ 10 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 10 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 10 (transLenTr ⟨70, by decide⟩ 10 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_10.D1 (m := 5) from colCertDiv_119_70_10.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 10 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_10.D2 (m := 5) from colCertDiv_119_70_10.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_10_match


theorem leaf_119_70_11 (hp : 11 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 11 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 11 (transLenTr ⟨70, by decide⟩ 11 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 11 (transLenTr ⟨70, by decide⟩ 11 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 11 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 11 (transLenTr ⟨70, by decide⟩ 11 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_11.D1 (m := 5) from colCertDiv_119_70_11.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 11 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_11.D2 (m := 5) from colCertDiv_119_70_11.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_11_match


theorem leaf_119_70_12 (hp : 12 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 12 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 12 (transLenTr ⟨70, by decide⟩ 12 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 12 (transLenTr ⟨70, by decide⟩ 12 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 12 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 12 (transLenTr ⟨70, by decide⟩ 12 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_12.D1 (m := 5) from colCertDiv_119_70_12.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 12 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_12.D2 (m := 5) from colCertDiv_119_70_12.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_12_match


theorem leaf_119_70_13 (hp : 13 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 13 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 13 (transLenTr ⟨70, by decide⟩ 13 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 13 (transLenTr ⟨70, by decide⟩ 13 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 13 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 13 (transLenTr ⟨70, by decide⟩ 13 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_13.D1 (m := 5) from colCertDiv_119_70_13.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 13 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_13.D2 (m := 5) from colCertDiv_119_70_13.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_13_match


theorem leaf_119_70_14 (hp : 14 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 14 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 14 (transLenTr ⟨70, by decide⟩ 14 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 14 (transLenTr ⟨70, by decide⟩ 14 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 14 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 14 (transLenTr ⟨70, by decide⟩ 14 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_14.D1 (m := 5) from colCertDiv_119_70_14.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 14 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_14.D2 (m := 5) from colCertDiv_119_70_14.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_14_match


theorem leaf_119_70_15 (hp : 15 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 15 (transLenTr ⟨70, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 15 (transLenTr ⟨70, by decide⟩ 15 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 15 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 15 (transLenTr ⟨70, by decide⟩ 15 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_15.D1 (m := 5) from colCertDiv_119_70_15.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 15 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_15.D2 (m := 5) from colCertDiv_119_70_15.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_15_match


theorem leaf_119_70_16 (hp : 16 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 16 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 16 (transLenTr ⟨70, by decide⟩ 16 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 16 (transLenTr ⟨70, by decide⟩ 16 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 16 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 16 (transLenTr ⟨70, by decide⟩ 16 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_16.D1 (m := 5) from colCertDiv_119_70_16.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 16 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_16.D2 (m := 5) from colCertDiv_119_70_16.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_16_match


theorem leaf_119_70_17 (hp : 17 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 17 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 17 (transLenTr ⟨70, by decide⟩ 17 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 17 (transLenTr ⟨70, by decide⟩ 17 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 17 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 17 (transLenTr ⟨70, by decide⟩ 17 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_17.D1 (m := 5) from colCertDiv_119_70_17.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 17 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_17.D2 (m := 5) from colCertDiv_119_70_17.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_17_match


theorem leaf_119_70_18 (hp : 18 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 18 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 18 (transLenTr ⟨70, by decide⟩ 18 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 18 (transLenTr ⟨70, by decide⟩ 18 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 18 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 18 (transLenTr ⟨70, by decide⟩ 18 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_18.D1 (m := 5) from colCertDiv_119_70_18.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 18 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_18.D2 (m := 5) from colCertDiv_119_70_18.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_18_match


theorem leaf_119_70_19 (hp : 19 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 19 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 19 (transLenTr ⟨70, by decide⟩ 19 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 19 (transLenTr ⟨70, by decide⟩ 19 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 19 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 19 (transLenTr ⟨70, by decide⟩ 19 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_19.D1 (m := 5) from colCertDiv_119_70_19.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 19 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_19.D2 (m := 5) from colCertDiv_119_70_19.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_19_match


theorem leaf_119_70_20 (hp : 20 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 20 (transLenTr ⟨70, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 20 (transLenTr ⟨70, by decide⟩ 20 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 20 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 20 (transLenTr ⟨70, by decide⟩ 20 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_20.D1 (m := 5) from colCertDiv_119_70_20.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 20 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_20.D2 (m := 5) from colCertDiv_119_70_20.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_20_match


theorem leaf_119_70_21 (hp : 21 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 21 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 21 (transLenTr ⟨70, by decide⟩ 21 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 21 (transLenTr ⟨70, by decide⟩ 21 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 21 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 21 (transLenTr ⟨70, by decide⟩ 21 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_21.D1 (m := 5) from colCertDiv_119_70_21.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 21 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_21.D2 (m := 5) from colCertDiv_119_70_21.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_21_match


theorem leaf_119_70_22 (hp : 22 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 22 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 22 (transLenTr ⟨70, by decide⟩ 22 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 22 (transLenTr ⟨70, by decide⟩ 22 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 22 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 22 (transLenTr ⟨70, by decide⟩ 22 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_22.D1 (m := 5) from colCertDiv_119_70_22.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 22 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_22.D2 (m := 5) from colCertDiv_119_70_22.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_22_match


theorem leaf_119_70_23 (hp : 23 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 23 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 23 (transLenTr ⟨70, by decide⟩ 23 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 23 (transLenTr ⟨70, by decide⟩ 23 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 23 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 23 (transLenTr ⟨70, by decide⟩ 23 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_23.D1 (m := 5) from colCertDiv_119_70_23.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 23 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_23.D2 (m := 5) from colCertDiv_119_70_23.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_23_match


theorem leaf_119_70_24 (hp : 24 < (Q2.transData.getD 70 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨70, by decide⟩ : Fin 148)) (colE2 ⟨70, by decide⟩ 24 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨70, by decide⟩ : Fin 148))
        (colE1 ⟨70, by decide⟩ 24 (transLenTr ⟨70, by decide⟩ 24 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨70, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨70, by decide⟩ 24 (transLenTr ⟨70, by decide⟩ 24 hp)) T119_70
      hfix119_70 hinj119_70 hcardT119_70
      (fun i => conj_mem_of_fixedPoints _ _ (T119_70 i) (hfix119_70 i) _)
      ⟨119, by decide⟩ ⟨70, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨70, by decide⟩ 24 hp) Q2.T119_70_2 Q2.hfix119_70_2 Q2.hinj119_70_2
      Q2.hcardT119_70_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_70_2 i) (Q2.hfix119_70_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨70, by decide⟩ 24 (transLenTr ⟨70, by decide⟩ 24 hp) : ↥(reps ⟨70, by decide⟩)) : Coordinate 1)
        T119_70 = colFn colCertDiv_119_70_24.D1 (m := 5) from colCertDiv_119_70_24.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨70, by decide⟩ 24 hp : ↥(Q2.reps ⟨70, by decide⟩)) : Coordinate 2)
        Q2.T119_70_2 = colFn colCertDiv_119_70_24.D2 (m := 5) from colCertDiv_119_70_24.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_70_24_match


theorem leaf_119_71_0 (hp : 0 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 0 (transLenTr ⟨71, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 0 (transLenTr ⟨71, by decide⟩ 0 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 0 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      colCert_119_71_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_71_1 (hp : 1 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 1 (transLenTr ⟨71, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 1 (transLenTr ⟨71, by decide⟩ 1 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 1 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      colCert_119_71_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_71_2 (hp : 2 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 2 (transLenTr ⟨71, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 2 (transLenTr ⟨71, by decide⟩ 2 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 2 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      colCert_119_71_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_71_3 (hp : 3 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 3 (transLenTr ⟨71, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 3 (transLenTr ⟨71, by decide⟩ 3 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 3 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      colCert_119_71_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_71_4 (hp : 4 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 4 (transLenTr ⟨71, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 4 (transLenTr ⟨71, by decide⟩ 4 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 4 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      colCert_119_71_4.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_71_5 (hp : 5 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 5 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 5 (transLenTr ⟨71, by decide⟩ 5 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 5 (transLenTr ⟨71, by decide⟩ 5 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 5 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 5 (transLenTr ⟨71, by decide⟩ 5 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_5.D1 (m := 5) from colCertDiv_119_71_5.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 5 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_5.D2 (m := 5) from colCertDiv_119_71_5.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_5_match


theorem leaf_119_71_6 (hp : 6 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 6 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 6 (transLenTr ⟨71, by decide⟩ 6 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 6 (transLenTr ⟨71, by decide⟩ 6 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 6 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 6 (transLenTr ⟨71, by decide⟩ 6 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_6.D1 (m := 5) from colCertDiv_119_71_6.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 6 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_6.D2 (m := 5) from colCertDiv_119_71_6.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_6_match


theorem leaf_119_71_7 (hp : 7 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 7 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 7 (transLenTr ⟨71, by decide⟩ 7 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 7 (transLenTr ⟨71, by decide⟩ 7 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 7 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 7 (transLenTr ⟨71, by decide⟩ 7 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_7.D1 (m := 5) from colCertDiv_119_71_7.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 7 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_7.D2 (m := 5) from colCertDiv_119_71_7.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_7_match


theorem leaf_119_71_8 (hp : 8 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 8 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 8 (transLenTr ⟨71, by decide⟩ 8 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 8 (transLenTr ⟨71, by decide⟩ 8 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 8 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 8 (transLenTr ⟨71, by decide⟩ 8 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_8.D1 (m := 5) from colCertDiv_119_71_8.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 8 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_8.D2 (m := 5) from colCertDiv_119_71_8.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_8_match


theorem leaf_119_71_9 (hp : 9 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 9 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 9 (transLenTr ⟨71, by decide⟩ 9 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 9 (transLenTr ⟨71, by decide⟩ 9 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 9 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 9 (transLenTr ⟨71, by decide⟩ 9 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_9.D1 (m := 5) from colCertDiv_119_71_9.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 9 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_9.D2 (m := 5) from colCertDiv_119_71_9.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_9_match


theorem leaf_119_71_10 (hp : 10 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 10 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 10 (transLenTr ⟨71, by decide⟩ 10 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 10 (transLenTr ⟨71, by decide⟩ 10 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 10 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 10 (transLenTr ⟨71, by decide⟩ 10 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_10.D1 (m := 5) from colCertDiv_119_71_10.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 10 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_10.D2 (m := 5) from colCertDiv_119_71_10.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_10_match


theorem leaf_119_71_11 (hp : 11 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 11 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 11 (transLenTr ⟨71, by decide⟩ 11 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 11 (transLenTr ⟨71, by decide⟩ 11 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 11 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 11 (transLenTr ⟨71, by decide⟩ 11 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_11.D1 (m := 5) from colCertDiv_119_71_11.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 11 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_11.D2 (m := 5) from colCertDiv_119_71_11.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_11_match


theorem leaf_119_71_12 (hp : 12 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 12 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 12 (transLenTr ⟨71, by decide⟩ 12 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 12 (transLenTr ⟨71, by decide⟩ 12 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 12 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 12 (transLenTr ⟨71, by decide⟩ 12 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_12.D1 (m := 5) from colCertDiv_119_71_12.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 12 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_12.D2 (m := 5) from colCertDiv_119_71_12.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_12_match


theorem leaf_119_71_13 (hp : 13 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 13 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 13 (transLenTr ⟨71, by decide⟩ 13 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 13 (transLenTr ⟨71, by decide⟩ 13 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 13 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 13 (transLenTr ⟨71, by decide⟩ 13 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_13.D1 (m := 5) from colCertDiv_119_71_13.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 13 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_13.D2 (m := 5) from colCertDiv_119_71_13.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_13_match


theorem leaf_119_71_14 (hp : 14 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 14 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 14 (transLenTr ⟨71, by decide⟩ 14 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 14 (transLenTr ⟨71, by decide⟩ 14 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 14 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 14 (transLenTr ⟨71, by decide⟩ 14 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_14.D1 (m := 5) from colCertDiv_119_71_14.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 14 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_14.D2 (m := 5) from colCertDiv_119_71_14.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_14_match


theorem leaf_119_71_15 (hp : 15 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 15 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 15 (transLenTr ⟨71, by decide⟩ 15 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 15 (transLenTr ⟨71, by decide⟩ 15 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 15 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 15 (transLenTr ⟨71, by decide⟩ 15 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_15.D1 (m := 5) from colCertDiv_119_71_15.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 15 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_15.D2 (m := 5) from colCertDiv_119_71_15.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_15_match


theorem leaf_119_71_16 (hp : 16 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 16 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 16 (transLenTr ⟨71, by decide⟩ 16 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 16 (transLenTr ⟨71, by decide⟩ 16 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 16 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 16 (transLenTr ⟨71, by decide⟩ 16 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_16.D1 (m := 5) from colCertDiv_119_71_16.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 16 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_16.D2 (m := 5) from colCertDiv_119_71_16.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_16_match


theorem leaf_119_71_17 (hp : 17 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 17 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 17 (transLenTr ⟨71, by decide⟩ 17 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 17 (transLenTr ⟨71, by decide⟩ 17 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 17 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 17 (transLenTr ⟨71, by decide⟩ 17 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_17.D1 (m := 5) from colCertDiv_119_71_17.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 17 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_17.D2 (m := 5) from colCertDiv_119_71_17.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_17_match


theorem leaf_119_71_18 (hp : 18 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 18 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 18 (transLenTr ⟨71, by decide⟩ 18 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 18 (transLenTr ⟨71, by decide⟩ 18 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 18 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 18 (transLenTr ⟨71, by decide⟩ 18 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_18.D1 (m := 5) from colCertDiv_119_71_18.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 18 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_18.D2 (m := 5) from colCertDiv_119_71_18.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_18_match


theorem leaf_119_71_19 (hp : 19 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 19 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 19 (transLenTr ⟨71, by decide⟩ 19 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 19 (transLenTr ⟨71, by decide⟩ 19 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 19 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 19 (transLenTr ⟨71, by decide⟩ 19 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_19.D1 (m := 5) from colCertDiv_119_71_19.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 19 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_19.D2 (m := 5) from colCertDiv_119_71_19.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_19_match


theorem leaf_119_71_20 (hp : 20 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 20 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 20 (transLenTr ⟨71, by decide⟩ 20 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 20 (transLenTr ⟨71, by decide⟩ 20 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 20 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 20 (transLenTr ⟨71, by decide⟩ 20 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_20.D1 (m := 5) from colCertDiv_119_71_20.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 20 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_20.D2 (m := 5) from colCertDiv_119_71_20.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_20_match


theorem leaf_119_71_21 (hp : 21 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 21 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 21 (transLenTr ⟨71, by decide⟩ 21 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 21 (transLenTr ⟨71, by decide⟩ 21 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 21 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 21 (transLenTr ⟨71, by decide⟩ 21 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_21.D1 (m := 5) from colCertDiv_119_71_21.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 21 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_21.D2 (m := 5) from colCertDiv_119_71_21.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_21_match


theorem leaf_119_71_22 (hp : 22 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 22 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 22 (transLenTr ⟨71, by decide⟩ 22 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 22 (transLenTr ⟨71, by decide⟩ 22 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 22 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 22 (transLenTr ⟨71, by decide⟩ 22 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_22.D1 (m := 5) from colCertDiv_119_71_22.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 22 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_22.D2 (m := 5) from colCertDiv_119_71_22.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_22_match


theorem leaf_119_71_23 (hp : 23 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 23 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 23 (transLenTr ⟨71, by decide⟩ 23 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 23 (transLenTr ⟨71, by decide⟩ 23 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 23 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 23 (transLenTr ⟨71, by decide⟩ 23 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_23.D1 (m := 5) from colCertDiv_119_71_23.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 23 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_23.D2 (m := 5) from colCertDiv_119_71_23.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_23_match


theorem leaf_119_71_24 (hp : 24 < (Q2.transData.getD 71 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨71, by decide⟩ : Fin 148)) (colE2 ⟨71, by decide⟩ 24 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨71, by decide⟩ : Fin 148))
        (colE1 ⟨71, by decide⟩ 24 (transLenTr ⟨71, by decide⟩ 24 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨119, by decide⟩ : Fin 148) ⟨71, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨71, by decide⟩ 24 (transLenTr ⟨71, by decide⟩ 24 hp)) T119_71
      hfix119_71 hinj119_71 hcardT119_71
      (fun i => conj_mem_of_fixedPoints _ _ (T119_71 i) (hfix119_71 i) _)
      ⟨119, by decide⟩ ⟨71, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨71, by decide⟩ 24 hp) Q2.T119_71_2 Q2.hfix119_71_2 Q2.hinj119_71_2
      Q2.hcardT119_71_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_71_2 i) (Q2.hfix119_71_2 i) _)
      ?_).symm
  rw [show colData1 (⟨119, by decide⟩ : Fin 148)
        ((colE1 ⟨71, by decide⟩ 24 (transLenTr ⟨71, by decide⟩ 24 hp) : ↥(reps ⟨71, by decide⟩)) : Coordinate 1)
        T119_71 = colFn colCertDiv_119_71_24.D1 (m := 5) from colCertDiv_119_71_24.bind1,
    show colData2 (⟨119, by decide⟩ : Fin 148)
        ((colE2 ⟨71, by decide⟩ 24 hp : ↥(Q2.reps ⟨71, by decide⟩)) : Coordinate 2)
        Q2.T119_71_2 = colFn colCertDiv_119_71_24.D2 (m := 5) from colCertDiv_119_71_24.bind2]
  rw [alnId_119 j hj]
  exact fastcode_of_div ⟨119, by decide⟩ _ _ _
    ((alnId_119 j hj) ▸ Q2.listedAt (⟨119, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨119, by decide⟩ : Fin 148) hj hq).1) colCertDiv_119_71_24_match


theorem leaf_119_72_0 (hp : 0 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 0 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 0 (transLenTr ⟨72, by decide⟩ 0 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 0 (transLenTr ⟨72, by decide⟩ 0 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 0 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      colCert_119_72_0.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_72_1 (hp : 1 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 1 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 1 (transLenTr ⟨72, by decide⟩ 1 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 1 (transLenTr ⟨72, by decide⟩ 1 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 1 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      colCert_119_72_1.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_72_2 (hp : 2 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 2 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 2 (transLenTr ⟨72, by decide⟩ 2 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 2 (transLenTr ⟨72, by decide⟩ 2 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 2 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      colCert_119_72_2.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_72_3 (hp : 3 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 3 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 3 (transLenTr ⟨72, by decide⟩ 3 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 3 (transLenTr ⟨72, by decide⟩ 3 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 3 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      colCert_119_72_3.hD ?_).symm
  rw [alnId_119 j hj]


theorem leaf_119_72_4 (hp : 4 < (Q2.transData.getD 72 []).length)
    (j : Nat) (hj : j < (repChars.getD 119 []).length)
    (hq : (normIsRep.getD 119 []).getD j false = true) :
    species (Q2.reps (⟨72, by decide⟩ : Fin 148)) (colE2 ⟨72, by decide⟩ 4 hp)
        (rowE2 (⟨119, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨72, by decide⟩ : Fin 148))
        (colE1 ⟨72, by decide⟩ 4 (transLenTr ⟨72, by decide⟩ 4 hp))
        (rowE1 (⟨119, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨119, by decide⟩ : Fin 148) ⟨72, by decide⟩ _
      (validAt ⟨119, by decide⟩ (listedAt ⟨119, by decide⟩ hj))
      (colE1 ⟨72, by decide⟩ 4 (transLenTr ⟨72, by decide⟩ 4 hp)) T119_72
      hfix119_72 hinj119_72 hcardT119_72
      (fun i => conj_mem_of_fixedPoints _ _ (T119_72 i) (hfix119_72 i) _)
      ⟨119, by decide⟩ ⟨72, by decide⟩ _
      (Q2.validAt ⟨119, by decide⟩ (Q2.listedAt ⟨119, by decide⟩
        (alnCheck_rep ⟨119, by decide⟩ hj hq).1))
      (colE2 ⟨72, by decide⟩ 4 hp) Q2.T119_72_2 Q2.hfix119_72_2 Q2.hinj119_72_2
      Q2.hcardT119_72_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T119_72_2 i) (Q2.hfix119_72_2 i) _)
      colCert_119_72_4.hD ?_).symm
  rw [alnId_119 j hj]


end LeanDring.P5Presentation
