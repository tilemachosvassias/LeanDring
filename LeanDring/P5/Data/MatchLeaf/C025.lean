/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C003
import LeanDring.P5.Data.ColRestCheap.C028
import LeanDring.P5.Data.ColRestCheap.C029
import LeanDring.P5.Data.ColRestCheap.C030
import LeanDring.P5.Data.ColRestCheap.C031
import LeanDring.P5.Data.ColRestCheap.C032
import LeanDring.P5.Data.ColTau.C001
import LeanDring.P5.Data.EntryK.C026
import LeanDring.P5.Data.EntryK.C027
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C032
import LeanDring.P5.Data.SpeciesDiv.C033
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk02

/-! # Stage-5 leaves, chunk 24 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_117_80_10 (hp : 10 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 10 (transLenTr ⟨80, by decide⟩ 10 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 10 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_15 (hp : 15 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 15 (transLenTr ⟨80, by decide⟩ 15 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 15 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_20 (hp : 20 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 20 (transLenTr ⟨80, by decide⟩ 20 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 20 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_25 (hp : 25 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 25 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 25 (transLenTr ⟨80, by decide⟩ 25 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 25 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_25.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_30 (hp : 30 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 30 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 30 (transLenTr ⟨80, by decide⟩ 30 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 30 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_30.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_35 (hp : 35 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 35 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 35 (transLenTr ⟨80, by decide⟩ 35 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 35 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_35.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_40 (hp : 40 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 40 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 40 (transLenTr ⟨80, by decide⟩ 40 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 40 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_40.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_45 (hp : 45 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 45 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 45 (transLenTr ⟨80, by decide⟩ 45 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 45 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_45.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_50 (hp : 50 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 50 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 50 (transLenTr ⟨80, by decide⟩ 50 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 50 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_50.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_55 (hp : 55 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 55 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 55 (transLenTr ⟨80, by decide⟩ 55 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 55 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_55.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_60 (hp : 60 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 60 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 60 (transLenTr ⟨80, by decide⟩ 60 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 60 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_60.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_65 (hp : 65 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 65 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 65 (transLenTr ⟨80, by decide⟩ 65 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 65 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_65.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_70 (hp : 70 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 70 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 70 (transLenTr ⟨80, by decide⟩ 70 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 70 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_70.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_75 (hp : 75 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 75 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 75 (transLenTr ⟨80, by decide⟩ 75 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 75 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_75.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_80 (hp : 80 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 80 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 80 (transLenTr ⟨80, by decide⟩ 80 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 80 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_80.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_85 (hp : 85 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 85 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 85 (transLenTr ⟨80, by decide⟩ 85 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 85 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_85.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_90 (hp : 90 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 90 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 90 (transLenTr ⟨80, by decide⟩ 90 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 90 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_90.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_95 (hp : 95 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 95 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 95 (transLenTr ⟨80, by decide⟩ 95 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 95 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_95.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_100 (hp : 100 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 100 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 100 (transLenTr ⟨80, by decide⟩ 100 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 100 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_100.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_105 (hp : 105 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 105 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 105 (transLenTr ⟨80, by decide⟩ 105 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 105 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_105.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_110 (hp : 110 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 110 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 110 (transLenTr ⟨80, by decide⟩ 110 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 110 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_110.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_115 (hp : 115 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 115 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 115 (transLenTr ⟨80, by decide⟩ 115 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 115 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_115.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_120 (hp : 120 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 120 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 120 (transLenTr ⟨80, by decide⟩ 120 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 120 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_120.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_91_0 (hp : 0 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 0 (transLenTr ⟨91, by decide⟩ 0 hp)) T117_91
      hfix117_91 hinj117_91 hcardT117_91
      (fun i => conj_mem_of_fixedPoints _ _ (T117_91 i) (hfix117_91 i) _)
      ⟨117, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 0 hp) Q2.T117_91_2 Q2.hfix117_91_2 Q2.hinj117_91_2
      Q2.hcardT117_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_91_2 i) (Q2.hfix117_91_2 i) _)
      colCert_117_91_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_91_1 (hp : 1 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 1 (transLenTr ⟨91, by decide⟩ 1 hp)) T117_91
      hfix117_91 hinj117_91 hcardT117_91
      (fun i => conj_mem_of_fixedPoints _ _ (T117_91 i) (hfix117_91 i) _)
      ⟨117, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 1 hp) Q2.T117_91_2 Q2.hfix117_91_2 Q2.hinj117_91_2
      Q2.hcardT117_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_91_2 i) (Q2.hfix117_91_2 i) _)
      colCert_117_91_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_91_2 (hp : 2 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 2 (transLenTr ⟨91, by decide⟩ 2 hp)) T117_91
      hfix117_91 hinj117_91 hcardT117_91
      (fun i => conj_mem_of_fixedPoints _ _ (T117_91 i) (hfix117_91 i) _)
      ⟨117, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 2 hp) Q2.T117_91_2 Q2.hfix117_91_2 Q2.hinj117_91_2
      Q2.hcardT117_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_91_2 i) (Q2.hfix117_91_2 i) _)
      colCert_117_91_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_91_3 (hp : 3 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 3 (transLenTr ⟨91, by decide⟩ 3 hp)) T117_91
      hfix117_91 hinj117_91 hcardT117_91
      (fun i => conj_mem_of_fixedPoints _ _ (T117_91 i) (hfix117_91 i) _)
      ⟨117, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 3 hp) Q2.T117_91_2 Q2.hfix117_91_2 Q2.hinj117_91_2
      Q2.hcardT117_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_91_2 i) (Q2.hfix117_91_2 i) _)
      colCert_117_91_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_91_4 (hp : 4 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 4 (transLenTr ⟨91, by decide⟩ 4 hp)) T117_91
      hfix117_91 hinj117_91 hcardT117_91
      (fun i => conj_mem_of_fixedPoints _ _ (T117_91 i) (hfix117_91 i) _)
      ⟨117, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 4 hp) Q2.T117_91_2 Q2.hfix117_91_2 Q2.hinj117_91_2
      Q2.hcardT117_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_91_2 i) (Q2.hfix117_91_2 i) _)
      colCert_117_91_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_91_5 (hp : 5 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 5 (transLenTr ⟨91, by decide⟩ 5 hp)) T117_91
      hfix117_91 hinj117_91 hcardT117_91
      (fun i => conj_mem_of_fixedPoints _ _ (T117_91 i) (hfix117_91 i) _)
      ⟨117, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 5 hp) Q2.T117_91_2 Q2.hfix117_91_2 Q2.hinj117_91_2
      Q2.hcardT117_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_91_2 i) (Q2.hfix117_91_2 i) _)
      colCert_117_91_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_91_10 (hp : 10 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 10 (transLenTr ⟨91, by decide⟩ 10 hp)) T117_91
      hfix117_91 hinj117_91 hcardT117_91
      (fun i => conj_mem_of_fixedPoints _ _ (T117_91 i) (hfix117_91 i) _)
      ⟨117, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 10 hp) Q2.T117_91_2 Q2.hfix117_91_2 Q2.hinj117_91_2
      Q2.hcardT117_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_91_2 i) (Q2.hfix117_91_2 i) _)
      colCert_117_91_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_91_15 (hp : 15 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 15 (transLenTr ⟨91, by decide⟩ 15 hp)) T117_91
      hfix117_91 hinj117_91 hcardT117_91
      (fun i => conj_mem_of_fixedPoints _ _ (T117_91 i) (hfix117_91 i) _)
      ⟨117, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 15 hp) Q2.T117_91_2 Q2.hfix117_91_2 Q2.hinj117_91_2
      Q2.hcardT117_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_91_2 i) (Q2.hfix117_91_2 i) _)
      colCert_117_91_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_91_20 (hp : 20 < (Q2.transData.getD 91 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨91, by decide⟩ : Fin 148)) (colE2 ⟨91, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨91, by decide⟩ : Fin 148))
        (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨91, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨91, by decide⟩ 20 (transLenTr ⟨91, by decide⟩ 20 hp)) T117_91
      hfix117_91 hinj117_91 hcardT117_91
      (fun i => conj_mem_of_fixedPoints _ _ (T117_91 i) (hfix117_91 i) _)
      ⟨117, by decide⟩ ⟨91, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨91, by decide⟩ 20 hp) Q2.T117_91_2 Q2.hfix117_91_2 Q2.hinj117_91_2
      Q2.hcardT117_91_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_91_2 i) (Q2.hfix117_91_2 i) _)
      colCert_117_91_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_96_0 (hp : 0 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 0 (transLenTr ⟨96, by decide⟩ 0 hp)) T117_96
      hfix117_96 hinj117_96 hcardT117_96
      (fun i => conj_mem_of_fixedPoints _ _ (T117_96 i) (hfix117_96 i) _)
      ⟨117, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 0 hp) Q2.T117_96_2 Q2.hfix117_96_2 Q2.hinj117_96_2
      Q2.hcardT117_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_96_2 i) (Q2.hfix117_96_2 i) _)
      colCert_117_96_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_96_1 (hp : 1 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 1 (transLenTr ⟨96, by decide⟩ 1 hp)) T117_96
      hfix117_96 hinj117_96 hcardT117_96
      (fun i => conj_mem_of_fixedPoints _ _ (T117_96 i) (hfix117_96 i) _)
      ⟨117, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 1 hp) Q2.T117_96_2 Q2.hfix117_96_2 Q2.hinj117_96_2
      Q2.hcardT117_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_96_2 i) (Q2.hfix117_96_2 i) _)
      colCert_117_96_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_96_2 (hp : 2 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 2 (transLenTr ⟨96, by decide⟩ 2 hp)) T117_96
      hfix117_96 hinj117_96 hcardT117_96
      (fun i => conj_mem_of_fixedPoints _ _ (T117_96 i) (hfix117_96 i) _)
      ⟨117, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 2 hp) Q2.T117_96_2 Q2.hfix117_96_2 Q2.hinj117_96_2
      Q2.hcardT117_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_96_2 i) (Q2.hfix117_96_2 i) _)
      colCert_117_96_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_96_3 (hp : 3 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 3 (transLenTr ⟨96, by decide⟩ 3 hp)) T117_96
      hfix117_96 hinj117_96 hcardT117_96
      (fun i => conj_mem_of_fixedPoints _ _ (T117_96 i) (hfix117_96 i) _)
      ⟨117, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 3 hp) Q2.T117_96_2 Q2.hfix117_96_2 Q2.hinj117_96_2
      Q2.hcardT117_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_96_2 i) (Q2.hfix117_96_2 i) _)
      colCert_117_96_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_96_4 (hp : 4 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 4 (transLenTr ⟨96, by decide⟩ 4 hp)) T117_96
      hfix117_96 hinj117_96 hcardT117_96
      (fun i => conj_mem_of_fixedPoints _ _ (T117_96 i) (hfix117_96 i) _)
      ⟨117, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 4 hp) Q2.T117_96_2 Q2.hfix117_96_2 Q2.hinj117_96_2
      Q2.hcardT117_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_96_2 i) (Q2.hfix117_96_2 i) _)
      colCert_117_96_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_96_5 (hp : 5 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 5 (transLenTr ⟨96, by decide⟩ 5 hp)) T117_96
      hfix117_96 hinj117_96 hcardT117_96
      (fun i => conj_mem_of_fixedPoints _ _ (T117_96 i) (hfix117_96 i) _)
      ⟨117, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 5 hp) Q2.T117_96_2 Q2.hfix117_96_2 Q2.hinj117_96_2
      Q2.hcardT117_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_96_2 i) (Q2.hfix117_96_2 i) _)
      colCert_117_96_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_96_10 (hp : 10 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 10 (transLenTr ⟨96, by decide⟩ 10 hp)) T117_96
      hfix117_96 hinj117_96 hcardT117_96
      (fun i => conj_mem_of_fixedPoints _ _ (T117_96 i) (hfix117_96 i) _)
      ⟨117, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 10 hp) Q2.T117_96_2 Q2.hfix117_96_2 Q2.hinj117_96_2
      Q2.hcardT117_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_96_2 i) (Q2.hfix117_96_2 i) _)
      colCert_117_96_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_96_15 (hp : 15 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 15 (transLenTr ⟨96, by decide⟩ 15 hp)) T117_96
      hfix117_96 hinj117_96 hcardT117_96
      (fun i => conj_mem_of_fixedPoints _ _ (T117_96 i) (hfix117_96 i) _)
      ⟨117, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 15 hp) Q2.T117_96_2 Q2.hfix117_96_2 Q2.hinj117_96_2
      Q2.hcardT117_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_96_2 i) (Q2.hfix117_96_2 i) _)
      colCert_117_96_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_96_20 (hp : 20 < (Q2.transData.getD 96 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨96, by decide⟩ : Fin 148)) (colE2 ⟨96, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨96, by decide⟩ : Fin 148))
        (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨96, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨96, by decide⟩ 20 (transLenTr ⟨96, by decide⟩ 20 hp)) T117_96
      hfix117_96 hinj117_96 hcardT117_96
      (fun i => conj_mem_of_fixedPoints _ _ (T117_96 i) (hfix117_96 i) _)
      ⟨117, by decide⟩ ⟨96, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨96, by decide⟩ 20 hp) Q2.T117_96_2 Q2.hfix117_96_2 Q2.hinj117_96_2
      Q2.hcardT117_96_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_96_2 i) (Q2.hfix117_96_2 i) _)
      colCert_117_96_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_101_0 (hp : 0 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 0 (transLenTr ⟨101, by decide⟩ 0 hp)) T117_101
      hfix117_101 hinj117_101 hcardT117_101
      (fun i => conj_mem_of_fixedPoints _ _ (T117_101 i) (hfix117_101 i) _)
      ⟨117, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 0 hp) Q2.T117_101_2 Q2.hfix117_101_2 Q2.hinj117_101_2
      Q2.hcardT117_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_101_2 i) (Q2.hfix117_101_2 i) _)
      colCert_117_101_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_101_1 (hp : 1 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 1 (transLenTr ⟨101, by decide⟩ 1 hp)) T117_101
      hfix117_101 hinj117_101 hcardT117_101
      (fun i => conj_mem_of_fixedPoints _ _ (T117_101 i) (hfix117_101 i) _)
      ⟨117, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 1 hp) Q2.T117_101_2 Q2.hfix117_101_2 Q2.hinj117_101_2
      Q2.hcardT117_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_101_2 i) (Q2.hfix117_101_2 i) _)
      colCert_117_101_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_101_2 (hp : 2 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 2 (transLenTr ⟨101, by decide⟩ 2 hp)) T117_101
      hfix117_101 hinj117_101 hcardT117_101
      (fun i => conj_mem_of_fixedPoints _ _ (T117_101 i) (hfix117_101 i) _)
      ⟨117, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 2 hp) Q2.T117_101_2 Q2.hfix117_101_2 Q2.hinj117_101_2
      Q2.hcardT117_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_101_2 i) (Q2.hfix117_101_2 i) _)
      colCert_117_101_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_101_3 (hp : 3 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 3 (transLenTr ⟨101, by decide⟩ 3 hp)) T117_101
      hfix117_101 hinj117_101 hcardT117_101
      (fun i => conj_mem_of_fixedPoints _ _ (T117_101 i) (hfix117_101 i) _)
      ⟨117, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 3 hp) Q2.T117_101_2 Q2.hfix117_101_2 Q2.hinj117_101_2
      Q2.hcardT117_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_101_2 i) (Q2.hfix117_101_2 i) _)
      colCert_117_101_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_101_4 (hp : 4 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 4 (transLenTr ⟨101, by decide⟩ 4 hp)) T117_101
      hfix117_101 hinj117_101 hcardT117_101
      (fun i => conj_mem_of_fixedPoints _ _ (T117_101 i) (hfix117_101 i) _)
      ⟨117, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 4 hp) Q2.T117_101_2 Q2.hfix117_101_2 Q2.hinj117_101_2
      Q2.hcardT117_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_101_2 i) (Q2.hfix117_101_2 i) _)
      colCert_117_101_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_101_5 (hp : 5 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 5 (transLenTr ⟨101, by decide⟩ 5 hp)) T117_101
      hfix117_101 hinj117_101 hcardT117_101
      (fun i => conj_mem_of_fixedPoints _ _ (T117_101 i) (hfix117_101 i) _)
      ⟨117, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 5 hp) Q2.T117_101_2 Q2.hfix117_101_2 Q2.hinj117_101_2
      Q2.hcardT117_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_101_2 i) (Q2.hfix117_101_2 i) _)
      colCert_117_101_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_101_10 (hp : 10 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 10 (transLenTr ⟨101, by decide⟩ 10 hp)) T117_101
      hfix117_101 hinj117_101 hcardT117_101
      (fun i => conj_mem_of_fixedPoints _ _ (T117_101 i) (hfix117_101 i) _)
      ⟨117, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 10 hp) Q2.T117_101_2 Q2.hfix117_101_2 Q2.hinj117_101_2
      Q2.hcardT117_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_101_2 i) (Q2.hfix117_101_2 i) _)
      colCert_117_101_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_101_15 (hp : 15 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 15 (transLenTr ⟨101, by decide⟩ 15 hp)) T117_101
      hfix117_101 hinj117_101 hcardT117_101
      (fun i => conj_mem_of_fixedPoints _ _ (T117_101 i) (hfix117_101 i) _)
      ⟨117, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 15 hp) Q2.T117_101_2 Q2.hfix117_101_2 Q2.hinj117_101_2
      Q2.hcardT117_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_101_2 i) (Q2.hfix117_101_2 i) _)
      colCert_117_101_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_101_20 (hp : 20 < (Q2.transData.getD 101 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨101, by decide⟩ : Fin 148)) (colE2 ⟨101, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨101, by decide⟩ : Fin 148))
        (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨101, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨101, by decide⟩ 20 (transLenTr ⟨101, by decide⟩ 20 hp)) T117_101
      hfix117_101 hinj117_101 hcardT117_101
      (fun i => conj_mem_of_fixedPoints _ _ (T117_101 i) (hfix117_101 i) _)
      ⟨117, by decide⟩ ⟨101, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨101, by decide⟩ 20 hp) Q2.T117_101_2 Q2.hfix117_101_2 Q2.hinj117_101_2
      Q2.hcardT117_101_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_101_2 i) (Q2.hfix117_101_2 i) _)
      colCert_117_101_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_106_0 (hp : 0 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 0 (transLenTr ⟨106, by decide⟩ 0 hp)) T117_106
      hfix117_106 hinj117_106 hcardT117_106
      (fun i => conj_mem_of_fixedPoints _ _ (T117_106 i) (hfix117_106 i) _)
      ⟨117, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 0 hp) Q2.T117_106_2 Q2.hfix117_106_2 Q2.hinj117_106_2
      Q2.hcardT117_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_106_2 i) (Q2.hfix117_106_2 i) _)
      colCert_117_106_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_106_1 (hp : 1 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 1 (transLenTr ⟨106, by decide⟩ 1 hp)) T117_106
      hfix117_106 hinj117_106 hcardT117_106
      (fun i => conj_mem_of_fixedPoints _ _ (T117_106 i) (hfix117_106 i) _)
      ⟨117, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 1 hp) Q2.T117_106_2 Q2.hfix117_106_2 Q2.hinj117_106_2
      Q2.hcardT117_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_106_2 i) (Q2.hfix117_106_2 i) _)
      colCert_117_106_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_106_2 (hp : 2 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 2 (transLenTr ⟨106, by decide⟩ 2 hp)) T117_106
      hfix117_106 hinj117_106 hcardT117_106
      (fun i => conj_mem_of_fixedPoints _ _ (T117_106 i) (hfix117_106 i) _)
      ⟨117, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 2 hp) Q2.T117_106_2 Q2.hfix117_106_2 Q2.hinj117_106_2
      Q2.hcardT117_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_106_2 i) (Q2.hfix117_106_2 i) _)
      colCert_117_106_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_106_3 (hp : 3 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 3 (transLenTr ⟨106, by decide⟩ 3 hp)) T117_106
      hfix117_106 hinj117_106 hcardT117_106
      (fun i => conj_mem_of_fixedPoints _ _ (T117_106 i) (hfix117_106 i) _)
      ⟨117, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 3 hp) Q2.T117_106_2 Q2.hfix117_106_2 Q2.hinj117_106_2
      Q2.hcardT117_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_106_2 i) (Q2.hfix117_106_2 i) _)
      colCert_117_106_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_106_4 (hp : 4 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 4 (transLenTr ⟨106, by decide⟩ 4 hp)) T117_106
      hfix117_106 hinj117_106 hcardT117_106
      (fun i => conj_mem_of_fixedPoints _ _ (T117_106 i) (hfix117_106 i) _)
      ⟨117, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 4 hp) Q2.T117_106_2 Q2.hfix117_106_2 Q2.hinj117_106_2
      Q2.hcardT117_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_106_2 i) (Q2.hfix117_106_2 i) _)
      colCert_117_106_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_106_5 (hp : 5 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 5 (transLenTr ⟨106, by decide⟩ 5 hp)) T117_106
      hfix117_106 hinj117_106 hcardT117_106
      (fun i => conj_mem_of_fixedPoints _ _ (T117_106 i) (hfix117_106 i) _)
      ⟨117, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 5 hp) Q2.T117_106_2 Q2.hfix117_106_2 Q2.hinj117_106_2
      Q2.hcardT117_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_106_2 i) (Q2.hfix117_106_2 i) _)
      colCert_117_106_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_106_10 (hp : 10 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 10 (transLenTr ⟨106, by decide⟩ 10 hp)) T117_106
      hfix117_106 hinj117_106 hcardT117_106
      (fun i => conj_mem_of_fixedPoints _ _ (T117_106 i) (hfix117_106 i) _)
      ⟨117, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 10 hp) Q2.T117_106_2 Q2.hfix117_106_2 Q2.hinj117_106_2
      Q2.hcardT117_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_106_2 i) (Q2.hfix117_106_2 i) _)
      colCert_117_106_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_106_15 (hp : 15 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 15 (transLenTr ⟨106, by decide⟩ 15 hp)) T117_106
      hfix117_106 hinj117_106 hcardT117_106
      (fun i => conj_mem_of_fixedPoints _ _ (T117_106 i) (hfix117_106 i) _)
      ⟨117, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 15 hp) Q2.T117_106_2 Q2.hfix117_106_2 Q2.hinj117_106_2
      Q2.hcardT117_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_106_2 i) (Q2.hfix117_106_2 i) _)
      colCert_117_106_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_106_20 (hp : 20 < (Q2.transData.getD 106 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨106, by decide⟩ : Fin 148)) (colE2 ⟨106, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨106, by decide⟩ : Fin 148))
        (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨106, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨106, by decide⟩ 20 (transLenTr ⟨106, by decide⟩ 20 hp)) T117_106
      hfix117_106 hinj117_106 hcardT117_106
      (fun i => conj_mem_of_fixedPoints _ _ (T117_106 i) (hfix117_106 i) _)
      ⟨117, by decide⟩ ⟨106, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨106, by decide⟩ 20 hp) Q2.T117_106_2 Q2.hfix117_106_2 Q2.hinj117_106_2
      Q2.hcardT117_106_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_106_2 i) (Q2.hfix117_106_2 i) _)
      colCert_117_106_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_111_0 (hp : 0 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 0 (transLenTr ⟨111, by decide⟩ 0 hp)) T117_111
      hfix117_111 hinj117_111 hcardT117_111
      (fun i => conj_mem_of_fixedPoints _ _ (T117_111 i) (hfix117_111 i) _)
      ⟨117, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 0 hp) Q2.T117_111_2 Q2.hfix117_111_2 Q2.hinj117_111_2
      Q2.hcardT117_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_111_2 i) (Q2.hfix117_111_2 i) _)
      colCert_117_111_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_111_1 (hp : 1 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 1 (transLenTr ⟨111, by decide⟩ 1 hp)) T117_111
      hfix117_111 hinj117_111 hcardT117_111
      (fun i => conj_mem_of_fixedPoints _ _ (T117_111 i) (hfix117_111 i) _)
      ⟨117, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 1 hp) Q2.T117_111_2 Q2.hfix117_111_2 Q2.hinj117_111_2
      Q2.hcardT117_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_111_2 i) (Q2.hfix117_111_2 i) _)
      colCert_117_111_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_111_2 (hp : 2 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 2 (transLenTr ⟨111, by decide⟩ 2 hp)) T117_111
      hfix117_111 hinj117_111 hcardT117_111
      (fun i => conj_mem_of_fixedPoints _ _ (T117_111 i) (hfix117_111 i) _)
      ⟨117, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 2 hp) Q2.T117_111_2 Q2.hfix117_111_2 Q2.hinj117_111_2
      Q2.hcardT117_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_111_2 i) (Q2.hfix117_111_2 i) _)
      colCert_117_111_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_111_3 (hp : 3 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 3 (transLenTr ⟨111, by decide⟩ 3 hp)) T117_111
      hfix117_111 hinj117_111 hcardT117_111
      (fun i => conj_mem_of_fixedPoints _ _ (T117_111 i) (hfix117_111 i) _)
      ⟨117, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 3 hp) Q2.T117_111_2 Q2.hfix117_111_2 Q2.hinj117_111_2
      Q2.hcardT117_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_111_2 i) (Q2.hfix117_111_2 i) _)
      colCert_117_111_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_111_4 (hp : 4 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 4 (transLenTr ⟨111, by decide⟩ 4 hp)) T117_111
      hfix117_111 hinj117_111 hcardT117_111
      (fun i => conj_mem_of_fixedPoints _ _ (T117_111 i) (hfix117_111 i) _)
      ⟨117, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 4 hp) Q2.T117_111_2 Q2.hfix117_111_2 Q2.hinj117_111_2
      Q2.hcardT117_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_111_2 i) (Q2.hfix117_111_2 i) _)
      colCert_117_111_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_111_5 (hp : 5 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 5 (transLenTr ⟨111, by decide⟩ 5 hp)) T117_111
      hfix117_111 hinj117_111 hcardT117_111
      (fun i => conj_mem_of_fixedPoints _ _ (T117_111 i) (hfix117_111 i) _)
      ⟨117, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 5 hp) Q2.T117_111_2 Q2.hfix117_111_2 Q2.hinj117_111_2
      Q2.hcardT117_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_111_2 i) (Q2.hfix117_111_2 i) _)
      colCert_117_111_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_111_10 (hp : 10 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 10 (transLenTr ⟨111, by decide⟩ 10 hp)) T117_111
      hfix117_111 hinj117_111 hcardT117_111
      (fun i => conj_mem_of_fixedPoints _ _ (T117_111 i) (hfix117_111 i) _)
      ⟨117, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 10 hp) Q2.T117_111_2 Q2.hfix117_111_2 Q2.hinj117_111_2
      Q2.hcardT117_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_111_2 i) (Q2.hfix117_111_2 i) _)
      colCert_117_111_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_111_15 (hp : 15 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 15 (transLenTr ⟨111, by decide⟩ 15 hp)) T117_111
      hfix117_111 hinj117_111 hcardT117_111
      (fun i => conj_mem_of_fixedPoints _ _ (T117_111 i) (hfix117_111 i) _)
      ⟨117, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 15 hp) Q2.T117_111_2 Q2.hfix117_111_2 Q2.hinj117_111_2
      Q2.hcardT117_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_111_2 i) (Q2.hfix117_111_2 i) _)
      colCert_117_111_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_111_20 (hp : 20 < (Q2.transData.getD 111 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨111, by decide⟩ : Fin 148)) (colE2 ⟨111, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨111, by decide⟩ : Fin 148))
        (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨111, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨111, by decide⟩ 20 (transLenTr ⟨111, by decide⟩ 20 hp)) T117_111
      hfix117_111 hinj117_111 hcardT117_111
      (fun i => conj_mem_of_fixedPoints _ _ (T117_111 i) (hfix117_111 i) _)
      ⟨117, by decide⟩ ⟨111, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨111, by decide⟩ 20 hp) Q2.T117_111_2 Q2.hfix117_111_2 Q2.hinj117_111_2
      Q2.hcardT117_111_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_111_2 i) (Q2.hfix117_111_2 i) _)
      colCert_117_111_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_0 (hp : 0 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 0 (transLenTr ⟨117, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 0 (transLenTr ⟨117, by decide⟩ 0 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 0 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_1 (hp : 1 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 1 (transLenTr ⟨117, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 1 (transLenTr ⟨117, by decide⟩ 1 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 1 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_2 (hp : 2 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 2 (transLenTr ⟨117, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 2 (transLenTr ⟨117, by decide⟩ 2 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 2 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_3 (hp : 3 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 3 (transLenTr ⟨117, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 3 (transLenTr ⟨117, by decide⟩ 3 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 3 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_4 (hp : 4 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 4 (transLenTr ⟨117, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 4 (transLenTr ⟨117, by decide⟩ 4 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 4 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_5 (hp : 5 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 5 (transLenTr ⟨117, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 5 (transLenTr ⟨117, by decide⟩ 5 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 5 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_6 (hp : 6 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 6 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 6 (transLenTr ⟨117, by decide⟩ 6 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 6 (transLenTr ⟨117, by decide⟩ 6 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 6 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_6.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_7 (hp : 7 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 7 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 7 (transLenTr ⟨117, by decide⟩ 7 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 7 (transLenTr ⟨117, by decide⟩ 7 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 7 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_7.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_8 (hp : 8 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 8 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 8 (transLenTr ⟨117, by decide⟩ 8 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 8 (transLenTr ⟨117, by decide⟩ 8 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 8 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_8.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_9 (hp : 9 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 9 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 9 (transLenTr ⟨117, by decide⟩ 9 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 9 (transLenTr ⟨117, by decide⟩ 9 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 9 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_9.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_10 (hp : 10 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 10 (transLenTr ⟨117, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 10 (transLenTr ⟨117, by decide⟩ 10 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 10 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_11 (hp : 11 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 11 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 11 (transLenTr ⟨117, by decide⟩ 11 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 11 (transLenTr ⟨117, by decide⟩ 11 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 11 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_11.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_12 (hp : 12 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 12 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 12 (transLenTr ⟨117, by decide⟩ 12 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 12 (transLenTr ⟨117, by decide⟩ 12 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 12 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_12.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_13 (hp : 13 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 13 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 13 (transLenTr ⟨117, by decide⟩ 13 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 13 (transLenTr ⟨117, by decide⟩ 13 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 13 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_13.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_14 (hp : 14 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 14 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 14 (transLenTr ⟨117, by decide⟩ 14 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 14 (transLenTr ⟨117, by decide⟩ 14 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 14 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_14.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_15 (hp : 15 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 15 (transLenTr ⟨117, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 15 (transLenTr ⟨117, by decide⟩ 15 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 15 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_16 (hp : 16 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 16 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 16 (transLenTr ⟨117, by decide⟩ 16 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 16 (transLenTr ⟨117, by decide⟩ 16 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 16 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_16.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_17 (hp : 17 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 17 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 17 (transLenTr ⟨117, by decide⟩ 17 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 17 (transLenTr ⟨117, by decide⟩ 17 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 17 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_17.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_18 (hp : 18 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 18 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 18 (transLenTr ⟨117, by decide⟩ 18 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 18 (transLenTr ⟨117, by decide⟩ 18 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 18 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_18.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_19 (hp : 19 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 19 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 19 (transLenTr ⟨117, by decide⟩ 19 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 19 (transLenTr ⟨117, by decide⟩ 19 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 19 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_19.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_20 (hp : 20 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 20 (transLenTr ⟨117, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 20 (transLenTr ⟨117, by decide⟩ 20 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 20 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_21 (hp : 21 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 21 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 21 (transLenTr ⟨117, by decide⟩ 21 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 21 (transLenTr ⟨117, by decide⟩ 21 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 21 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_21.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_22 (hp : 22 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 22 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 22 (transLenTr ⟨117, by decide⟩ 22 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 22 (transLenTr ⟨117, by decide⟩ 22 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 22 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_22.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_23 (hp : 23 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 23 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 23 (transLenTr ⟨117, by decide⟩ 23 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 23 (transLenTr ⟨117, by decide⟩ 23 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 23 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_23.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_24 (hp : 24 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 24 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 24 (transLenTr ⟨117, by decide⟩ 24 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 24 (transLenTr ⟨117, by decide⟩ 24 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 24 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_24.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_25 (hp : 25 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 25 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 25 (transLenTr ⟨117, by decide⟩ 25 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 25 (transLenTr ⟨117, by decide⟩ 25 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 25 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_25.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_30 (hp : 30 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 30 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 30 (transLenTr ⟨117, by decide⟩ 30 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 30 (transLenTr ⟨117, by decide⟩ 30 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 30 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_30.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_35 (hp : 35 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 35 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 35 (transLenTr ⟨117, by decide⟩ 35 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 35 (transLenTr ⟨117, by decide⟩ 35 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 35 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_35.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_40 (hp : 40 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 40 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 40 (transLenTr ⟨117, by decide⟩ 40 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 40 (transLenTr ⟨117, by decide⟩ 40 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 40 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_40.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_45 (hp : 45 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 45 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 45 (transLenTr ⟨117, by decide⟩ 45 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 45 (transLenTr ⟨117, by decide⟩ 45 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 45 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_45.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_50 (hp : 50 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 50 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 50 (transLenTr ⟨117, by decide⟩ 50 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 50 (transLenTr ⟨117, by decide⟩ 50 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 50 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_50.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_55 (hp : 55 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 55 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 55 (transLenTr ⟨117, by decide⟩ 55 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 55 (transLenTr ⟨117, by decide⟩ 55 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 55 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_55.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_60 (hp : 60 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 60 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 60 (transLenTr ⟨117, by decide⟩ 60 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 60 (transLenTr ⟨117, by decide⟩ 60 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 60 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_60.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_65 (hp : 65 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 65 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 65 (transLenTr ⟨117, by decide⟩ 65 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 65 (transLenTr ⟨117, by decide⟩ 65 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 65 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_65.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_70 (hp : 70 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 70 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 70 (transLenTr ⟨117, by decide⟩ 70 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 70 (transLenTr ⟨117, by decide⟩ 70 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 70 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_70.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_75 (hp : 75 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 75 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 75 (transLenTr ⟨117, by decide⟩ 75 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 75 (transLenTr ⟨117, by decide⟩ 75 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 75 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_75.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_80 (hp : 80 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 80 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 80 (transLenTr ⟨117, by decide⟩ 80 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 80 (transLenTr ⟨117, by decide⟩ 80 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 80 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_80.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_85 (hp : 85 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 85 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 85 (transLenTr ⟨117, by decide⟩ 85 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 85 (transLenTr ⟨117, by decide⟩ 85 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 85 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_85.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_90 (hp : 90 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 90 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 90 (transLenTr ⟨117, by decide⟩ 90 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 90 (transLenTr ⟨117, by decide⟩ 90 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 90 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_90.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_95 (hp : 95 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 95 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 95 (transLenTr ⟨117, by decide⟩ 95 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 95 (transLenTr ⟨117, by decide⟩ 95 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 95 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_95.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_100 (hp : 100 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 100 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 100 (transLenTr ⟨117, by decide⟩ 100 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 100 (transLenTr ⟨117, by decide⟩ 100 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 100 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_100.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_105 (hp : 105 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 105 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 105 (transLenTr ⟨117, by decide⟩ 105 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 105 (transLenTr ⟨117, by decide⟩ 105 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 105 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_105.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_110 (hp : 110 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 110 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 110 (transLenTr ⟨117, by decide⟩ 110 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 110 (transLenTr ⟨117, by decide⟩ 110 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 110 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_110.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_115 (hp : 115 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 115 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 115 (transLenTr ⟨117, by decide⟩ 115 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 115 (transLenTr ⟨117, by decide⟩ 115 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 115 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_115.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_117_120 (hp : 120 < (Q2.transData.getD 117 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨117, by decide⟩ : Fin 148)) (colE2 ⟨117, by decide⟩ 120 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨117, by decide⟩ : Fin 148))
        (colE1 ⟨117, by decide⟩ 120 (transLenTr ⟨117, by decide⟩ 120 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨117, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨117, by decide⟩ 120 (transLenTr ⟨117, by decide⟩ 120 hp)) T117_117
      hfix117_117 hinj117_117 hcardT117_117
      (fun i => conj_mem_of_fixedPoints _ _ (T117_117 i) (hfix117_117 i) _)
      ⟨117, by decide⟩ ⟨117, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨117, by decide⟩ 120 hp) Q2.T117_117_2 Q2.hfix117_117_2 Q2.hinj117_117_2
      Q2.hcardT117_117_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_117_2 i) (Q2.hfix117_117_2 i) _)
      colCert_117_117_120.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_118_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T118_1
      hfix118_1 hinj118_1 hcardT118_1
      (fun i => conj_mem_of_fixedPoints _ _ (T118_1 i) (hfix118_1 i) _)
      ⟨118, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T118_1_2 Q2.hfix118_1_2 Q2.hinj118_1_2
      Q2.hcardT118_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_1_2 i) (Q2.hfix118_1_2 i) _)
      colCert_118_1_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T118_1
      hfix118_1 hinj118_1 hcardT118_1
      (fun i => conj_mem_of_fixedPoints _ _ (T118_1 i) (hfix118_1 i) _)
      ⟨118, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T118_1_2 Q2.hfix118_1_2 Q2.hinj118_1_2
      Q2.hcardT118_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_1_2 i) (Q2.hfix118_1_2 i) _)
      colCert_118_1_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T118_1
      hfix118_1 hinj118_1 hcardT118_1
      (fun i => conj_mem_of_fixedPoints _ _ (T118_1 i) (hfix118_1 i) _)
      ⟨118, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T118_1_2 Q2.hfix118_1_2 Q2.hinj118_1_2
      Q2.hcardT118_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_1_2 i) (Q2.hfix118_1_2 i) _)
      colCert_118_1_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T118_1
      hfix118_1 hinj118_1 hcardT118_1
      (fun i => conj_mem_of_fixedPoints _ _ (T118_1 i) (hfix118_1 i) _)
      ⟨118, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T118_1_2 Q2.hfix118_1_2 Q2.hinj118_1_2
      Q2.hcardT118_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_1_2 i) (Q2.hfix118_1_2 i) _)
      colCert_118_1_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T118_1
      hfix118_1 hinj118_1 hcardT118_1
      (fun i => conj_mem_of_fixedPoints _ _ (T118_1 i) (hfix118_1 i) _)
      ⟨118, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T118_1_2 Q2.hfix118_1_2 Q2.hinj118_1_2
      Q2.hcardT118_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_1_2 i) (Q2.hfix118_1_2 i) _)
      colCert_118_1_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T118_6
      hfix118_6 hinj118_6 hcardT118_6
      (fun i => conj_mem_of_fixedPoints _ _ (T118_6 i) (hfix118_6 i) _)
      ⟨118, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T118_6_2 Q2.hfix118_6_2 Q2.hinj118_6_2
      Q2.hcardT118_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_6_2 i) (Q2.hfix118_6_2 i) _)
      colCert_118_6_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T118_6
      hfix118_6 hinj118_6 hcardT118_6
      (fun i => conj_mem_of_fixedPoints _ _ (T118_6 i) (hfix118_6 i) _)
      ⟨118, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T118_6_2 Q2.hfix118_6_2 Q2.hinj118_6_2
      Q2.hcardT118_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_6_2 i) (Q2.hfix118_6_2 i) _)
      colCert_118_6_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T118_6
      hfix118_6 hinj118_6 hcardT118_6
      (fun i => conj_mem_of_fixedPoints _ _ (T118_6 i) (hfix118_6 i) _)
      ⟨118, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T118_6_2 Q2.hfix118_6_2 Q2.hinj118_6_2
      Q2.hcardT118_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_6_2 i) (Q2.hfix118_6_2 i) _)
      colCert_118_6_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T118_6
      hfix118_6 hinj118_6 hcardT118_6
      (fun i => conj_mem_of_fixedPoints _ _ (T118_6 i) (hfix118_6 i) _)
      ⟨118, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T118_6_2 Q2.hfix118_6_2 Q2.hinj118_6_2
      Q2.hcardT118_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_6_2 i) (Q2.hfix118_6_2 i) _)
      colCert_118_6_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T118_6
      hfix118_6 hinj118_6 hcardT118_6
      (fun i => conj_mem_of_fixedPoints _ _ (T118_6 i) (hfix118_6 i) _)
      ⟨118, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T118_6_2 Q2.hfix118_6_2 Q2.hinj118_6_2
      Q2.hcardT118_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_6_2 i) (Q2.hfix118_6_2 i) _)
      colCert_118_6_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T118_7
      hfix118_7 hinj118_7 hcardT118_7
      (fun i => conj_mem_of_fixedPoints _ _ (T118_7 i) (hfix118_7 i) _)
      ⟨118, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T118_7_2 Q2.hfix118_7_2 Q2.hinj118_7_2
      Q2.hcardT118_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_7_2 i) (Q2.hfix118_7_2 i) _)
      colCert_118_7_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T118_7
      hfix118_7 hinj118_7 hcardT118_7
      (fun i => conj_mem_of_fixedPoints _ _ (T118_7 i) (hfix118_7 i) _)
      ⟨118, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T118_7_2 Q2.hfix118_7_2 Q2.hinj118_7_2
      Q2.hcardT118_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_7_2 i) (Q2.hfix118_7_2 i) _)
      colCert_118_7_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T118_7
      hfix118_7 hinj118_7 hcardT118_7
      (fun i => conj_mem_of_fixedPoints _ _ (T118_7 i) (hfix118_7 i) _)
      ⟨118, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T118_7_2 Q2.hfix118_7_2 Q2.hinj118_7_2
      Q2.hcardT118_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_7_2 i) (Q2.hfix118_7_2 i) _)
      colCert_118_7_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T118_7
      hfix118_7 hinj118_7 hcardT118_7
      (fun i => conj_mem_of_fixedPoints _ _ (T118_7 i) (hfix118_7 i) _)
      ⟨118, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T118_7_2 Q2.hfix118_7_2 Q2.hinj118_7_2
      Q2.hcardT118_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_7_2 i) (Q2.hfix118_7_2 i) _)
      colCert_118_7_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T118_7
      hfix118_7 hinj118_7 hcardT118_7
      (fun i => conj_mem_of_fixedPoints _ _ (T118_7 i) (hfix118_7 i) _)
      ⟨118, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T118_7_2 Q2.hfix118_7_2 Q2.hinj118_7_2
      Q2.hcardT118_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_7_2 i) (Q2.hfix118_7_2 i) _)
      colCert_118_7_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T118_8
      hfix118_8 hinj118_8 hcardT118_8
      (fun i => conj_mem_of_fixedPoints _ _ (T118_8 i) (hfix118_8 i) _)
      ⟨118, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T118_8_2 Q2.hfix118_8_2 Q2.hinj118_8_2
      Q2.hcardT118_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_8_2 i) (Q2.hfix118_8_2 i) _)
      colCert_118_8_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T118_8
      hfix118_8 hinj118_8 hcardT118_8
      (fun i => conj_mem_of_fixedPoints _ _ (T118_8 i) (hfix118_8 i) _)
      ⟨118, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T118_8_2 Q2.hfix118_8_2 Q2.hinj118_8_2
      Q2.hcardT118_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_8_2 i) (Q2.hfix118_8_2 i) _)
      colCert_118_8_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T118_8
      hfix118_8 hinj118_8 hcardT118_8
      (fun i => conj_mem_of_fixedPoints _ _ (T118_8 i) (hfix118_8 i) _)
      ⟨118, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T118_8_2 Q2.hfix118_8_2 Q2.hinj118_8_2
      Q2.hcardT118_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_8_2 i) (Q2.hfix118_8_2 i) _)
      colCert_118_8_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T118_8
      hfix118_8 hinj118_8 hcardT118_8
      (fun i => conj_mem_of_fixedPoints _ _ (T118_8 i) (hfix118_8 i) _)
      ⟨118, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T118_8_2 Q2.hfix118_8_2 Q2.hinj118_8_2
      Q2.hcardT118_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_8_2 i) (Q2.hfix118_8_2 i) _)
      colCert_118_8_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T118_8
      hfix118_8 hinj118_8 hcardT118_8
      (fun i => conj_mem_of_fixedPoints _ _ (T118_8 i) (hfix118_8 i) _)
      ⟨118, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T118_8_2 Q2.hfix118_8_2 Q2.hinj118_8_2
      Q2.hcardT118_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_8_2 i) (Q2.hfix118_8_2 i) _)
      colCert_118_8_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_9_0 (hp : 0 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 0 (transLenTr ⟨9, by decide⟩ 0 hp)) T118_9
      hfix118_9 hinj118_9 hcardT118_9
      (fun i => conj_mem_of_fixedPoints _ _ (T118_9 i) (hfix118_9 i) _)
      ⟨118, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 0 hp) Q2.T118_9_2 Q2.hfix118_9_2 Q2.hinj118_9_2
      Q2.hcardT118_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_9_2 i) (Q2.hfix118_9_2 i) _)
      colCert_118_9_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_9_1 (hp : 1 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 1 (transLenTr ⟨9, by decide⟩ 1 hp)) T118_9
      hfix118_9 hinj118_9 hcardT118_9
      (fun i => conj_mem_of_fixedPoints _ _ (T118_9 i) (hfix118_9 i) _)
      ⟨118, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 1 hp) Q2.T118_9_2 Q2.hfix118_9_2 Q2.hinj118_9_2
      Q2.hcardT118_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_9_2 i) (Q2.hfix118_9_2 i) _)
      colCert_118_9_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_9_2 (hp : 2 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 2 (transLenTr ⟨9, by decide⟩ 2 hp)) T118_9
      hfix118_9 hinj118_9 hcardT118_9
      (fun i => conj_mem_of_fixedPoints _ _ (T118_9 i) (hfix118_9 i) _)
      ⟨118, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 2 hp) Q2.T118_9_2 Q2.hfix118_9_2 Q2.hinj118_9_2
      Q2.hcardT118_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_9_2 i) (Q2.hfix118_9_2 i) _)
      colCert_118_9_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_9_3 (hp : 3 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 3 (transLenTr ⟨9, by decide⟩ 3 hp)) T118_9
      hfix118_9 hinj118_9 hcardT118_9
      (fun i => conj_mem_of_fixedPoints _ _ (T118_9 i) (hfix118_9 i) _)
      ⟨118, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 3 hp) Q2.T118_9_2 Q2.hfix118_9_2 Q2.hinj118_9_2
      Q2.hcardT118_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_9_2 i) (Q2.hfix118_9_2 i) _)
      colCert_118_9_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_9_4 (hp : 4 < (Q2.transData.getD 9 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨9, by decide⟩ : Fin 148)) (colE2 ⟨9, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨9, by decide⟩ : Fin 148))
        (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨9, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨9, by decide⟩ 4 (transLenTr ⟨9, by decide⟩ 4 hp)) T118_9
      hfix118_9 hinj118_9 hcardT118_9
      (fun i => conj_mem_of_fixedPoints _ _ (T118_9 i) (hfix118_9 i) _)
      ⟨118, by decide⟩ ⟨9, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨9, by decide⟩ 4 hp) Q2.T118_9_2 Q2.hfix118_9_2 Q2.hinj118_9_2
      Q2.hcardT118_9_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_9_2 i) (Q2.hfix118_9_2 i) _)
      colCert_118_9_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_10_0 (hp : 0 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 0 (transLenTr ⟨10, by decide⟩ 0 hp)) T118_10
      hfix118_10 hinj118_10 hcardT118_10
      (fun i => conj_mem_of_fixedPoints _ _ (T118_10 i) (hfix118_10 i) _)
      ⟨118, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 0 hp) Q2.T118_10_2 Q2.hfix118_10_2 Q2.hinj118_10_2
      Q2.hcardT118_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_10_2 i) (Q2.hfix118_10_2 i) _)
      colCert_118_10_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_10_1 (hp : 1 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 1 (transLenTr ⟨10, by decide⟩ 1 hp)) T118_10
      hfix118_10 hinj118_10 hcardT118_10
      (fun i => conj_mem_of_fixedPoints _ _ (T118_10 i) (hfix118_10 i) _)
      ⟨118, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 1 hp) Q2.T118_10_2 Q2.hfix118_10_2 Q2.hinj118_10_2
      Q2.hcardT118_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_10_2 i) (Q2.hfix118_10_2 i) _)
      colCert_118_10_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_10_2 (hp : 2 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 2 (transLenTr ⟨10, by decide⟩ 2 hp)) T118_10
      hfix118_10 hinj118_10 hcardT118_10
      (fun i => conj_mem_of_fixedPoints _ _ (T118_10 i) (hfix118_10 i) _)
      ⟨118, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 2 hp) Q2.T118_10_2 Q2.hfix118_10_2 Q2.hinj118_10_2
      Q2.hcardT118_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_10_2 i) (Q2.hfix118_10_2 i) _)
      colCert_118_10_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_10_3 (hp : 3 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 3 (transLenTr ⟨10, by decide⟩ 3 hp)) T118_10
      hfix118_10 hinj118_10 hcardT118_10
      (fun i => conj_mem_of_fixedPoints _ _ (T118_10 i) (hfix118_10 i) _)
      ⟨118, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 3 hp) Q2.T118_10_2 Q2.hfix118_10_2 Q2.hinj118_10_2
      Q2.hcardT118_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_10_2 i) (Q2.hfix118_10_2 i) _)
      colCert_118_10_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_10_4 (hp : 4 < (Q2.transData.getD 10 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨10, by decide⟩ : Fin 148)) (colE2 ⟨10, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨10, by decide⟩ : Fin 148))
        (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨10, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨10, by decide⟩ 4 (transLenTr ⟨10, by decide⟩ 4 hp)) T118_10
      hfix118_10 hinj118_10 hcardT118_10
      (fun i => conj_mem_of_fixedPoints _ _ (T118_10 i) (hfix118_10 i) _)
      ⟨118, by decide⟩ ⟨10, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨10, by decide⟩ 4 hp) Q2.T118_10_2 Q2.hfix118_10_2 Q2.hinj118_10_2
      Q2.hcardT118_10_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_10_2 i) (Q2.hfix118_10_2 i) _)
      colCert_118_10_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T118_12
      hfix118_12 hinj118_12 hcardT118_12
      (fun i => conj_mem_of_fixedPoints _ _ (T118_12 i) (hfix118_12 i) _)
      ⟨118, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T118_12_2 Q2.hfix118_12_2 Q2.hinj118_12_2
      Q2.hcardT118_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_12_2 i) (Q2.hfix118_12_2 i) _)
      colCert_118_12_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T118_12
      hfix118_12 hinj118_12 hcardT118_12
      (fun i => conj_mem_of_fixedPoints _ _ (T118_12 i) (hfix118_12 i) _)
      ⟨118, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T118_12_2 Q2.hfix118_12_2 Q2.hinj118_12_2
      Q2.hcardT118_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_12_2 i) (Q2.hfix118_12_2 i) _)
      colCert_118_12_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T118_12
      hfix118_12 hinj118_12 hcardT118_12
      (fun i => conj_mem_of_fixedPoints _ _ (T118_12 i) (hfix118_12 i) _)
      ⟨118, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T118_12_2 Q2.hfix118_12_2 Q2.hinj118_12_2
      Q2.hcardT118_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_12_2 i) (Q2.hfix118_12_2 i) _)
      colCert_118_12_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T118_12
      hfix118_12 hinj118_12 hcardT118_12
      (fun i => conj_mem_of_fixedPoints _ _ (T118_12 i) (hfix118_12 i) _)
      ⟨118, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T118_12_2 Q2.hfix118_12_2 Q2.hinj118_12_2
      Q2.hcardT118_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_12_2 i) (Q2.hfix118_12_2 i) _)
      colCert_118_12_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T118_12
      hfix118_12 hinj118_12 hcardT118_12
      (fun i => conj_mem_of_fixedPoints _ _ (T118_12 i) (hfix118_12 i) _)
      ⟨118, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T118_12_2 Q2.hfix118_12_2 Q2.hinj118_12_2
      Q2.hcardT118_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_12_2 i) (Q2.hfix118_12_2 i) _)
      colCert_118_12_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_0 (hp : 0 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 0 (transLenTr ⟨13, by decide⟩ 0 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 0 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_1 (hp : 1 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 1 (transLenTr ⟨13, by decide⟩ 1 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 1 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_2 (hp : 2 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 2 (transLenTr ⟨13, by decide⟩ 2 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 2 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_3 (hp : 3 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 3 (transLenTr ⟨13, by decide⟩ 3 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 3 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_4 (hp : 4 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 4 (transLenTr ⟨13, by decide⟩ 4 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 4 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_5 (hp : 5 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 5 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 5 (transLenTr ⟨13, by decide⟩ 5 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T118_13 = colFn colCertDiv_118_13_5.D1 (m := 5) from colCertDiv_118_13_5.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 5 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T118_13_2 = colFn colCertDiv_118_13_5.D2 (m := 5) from colCertDiv_118_13_5.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_tau ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_13_5_tau_match


theorem leaf_118_13_6 (hp : 6 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 6 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 6 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 6 (transLenTr ⟨13, by decide⟩ 6 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T118_13 = colFn colCertDiv_118_13_6.D1 (m := 5) from colCertDiv_118_13_6.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 6 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T118_13_2 = colFn colCertDiv_118_13_6.D2 (m := 5) from colCertDiv_118_13_6.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_tau ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_13_6_tau_match


theorem leaf_118_13_7 (hp : 7 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 7 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 7 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 7 (transLenTr ⟨13, by decide⟩ 7 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T118_13 = colFn colCertDiv_118_13_7.D1 (m := 5) from colCertDiv_118_13_7.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 7 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T118_13_2 = colFn colCertDiv_118_13_7.D2 (m := 5) from colCertDiv_118_13_7.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_tau ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_13_7_tau_match


theorem leaf_118_13_8 (hp : 8 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 8 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 8 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨13, by decide⟩ 8 (transLenTr ⟨13, by decide⟩ 8 hp) : ↥(reps ⟨13, by decide⟩)) : Coordinate 1)
        T118_13 = colFn colCertDiv_118_13_8.D1 (m := 5) from colCertDiv_118_13_8.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨13, by decide⟩ 8 hp : ↥(Q2.reps ⟨13, by decide⟩)) : Coordinate 2)
        Q2.T118_13_2 = colFn colCertDiv_118_13_8.D2 (m := 5) from colCertDiv_118_13_8.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_tau ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_13_8_tau_match


theorem leaf_118_13_9 (hp : 9 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 9 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 9 (transLenTr ⟨13, by decide⟩ 9 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 9 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_9.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_10 (hp : 10 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 10 (transLenTr ⟨13, by decide⟩ 10 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 10 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_11 (hp : 11 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 11 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 11 (transLenTr ⟨13, by decide⟩ 11 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 11 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_11.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_12 (hp : 12 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 12 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 12 (transLenTr ⟨13, by decide⟩ 12 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 12 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_12.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_13 (hp : 13 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 13 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 13 (transLenTr ⟨13, by decide⟩ 13 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 13 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_13.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_14 (hp : 14 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 14 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 14 (transLenTr ⟨13, by decide⟩ 14 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 14 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_14.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_15 (hp : 15 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 15 (transLenTr ⟨13, by decide⟩ 15 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 15 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_16 (hp : 16 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 16 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 16 (transLenTr ⟨13, by decide⟩ 16 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 16 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_16.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_17 (hp : 17 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 17 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 17 (transLenTr ⟨13, by decide⟩ 17 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 17 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_17.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_18 (hp : 18 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 18 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 18 (transLenTr ⟨13, by decide⟩ 18 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 18 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_18.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_19 (hp : 19 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 19 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 19 (transLenTr ⟨13, by decide⟩ 19 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 19 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_19.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_20 (hp : 20 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 20 (transLenTr ⟨13, by decide⟩ 20 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 20 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_21 (hp : 21 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 21 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 21 (transLenTr ⟨13, by decide⟩ 21 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 21 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_21.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_22 (hp : 22 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 22 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 22 (transLenTr ⟨13, by decide⟩ 22 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 22 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_22.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_23 (hp : 23 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 23 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 23 (transLenTr ⟨13, by decide⟩ 23 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 23 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_23.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_13_24 (hp : 24 < (Q2.transData.getD 13 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨13, by decide⟩ : Fin 148)) (colE2 ⟨13, by decide⟩ 24 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨13, by decide⟩ : Fin 148))
        (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨13, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨13, by decide⟩ 24 (transLenTr ⟨13, by decide⟩ 24 hp)) T118_13
      hfix118_13 hinj118_13 hcardT118_13
      (fun i => conj_mem_of_fixedPoints _ _ (T118_13 i) (hfix118_13 i) _)
      ⟨118, by decide⟩ ⟨13, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨13, by decide⟩ 24 hp) Q2.T118_13_2 Q2.hfix118_13_2 Q2.hinj118_13_2
      Q2.hcardT118_13_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_13_2 i) (Q2.hfix118_13_2 i) _)
      colCert_118_13_24.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T118_19
      hfix118_19 hinj118_19 hcardT118_19
      (fun i => conj_mem_of_fixedPoints _ _ (T118_19 i) (hfix118_19 i) _)
      ⟨118, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T118_19_2 Q2.hfix118_19_2 Q2.hinj118_19_2
      Q2.hcardT118_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_19_2 i) (Q2.hfix118_19_2 i) _)
      colCert_118_19_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T118_19
      hfix118_19 hinj118_19 hcardT118_19
      (fun i => conj_mem_of_fixedPoints _ _ (T118_19 i) (hfix118_19 i) _)
      ⟨118, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T118_19_2 Q2.hfix118_19_2 Q2.hinj118_19_2
      Q2.hcardT118_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_19_2 i) (Q2.hfix118_19_2 i) _)
      colCert_118_19_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T118_19
      hfix118_19 hinj118_19 hcardT118_19
      (fun i => conj_mem_of_fixedPoints _ _ (T118_19 i) (hfix118_19 i) _)
      ⟨118, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T118_19_2 Q2.hfix118_19_2 Q2.hinj118_19_2
      Q2.hcardT118_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_19_2 i) (Q2.hfix118_19_2 i) _)
      colCert_118_19_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T118_19
      hfix118_19 hinj118_19 hcardT118_19
      (fun i => conj_mem_of_fixedPoints _ _ (T118_19 i) (hfix118_19 i) _)
      ⟨118, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T118_19_2 Q2.hfix118_19_2 Q2.hinj118_19_2
      Q2.hcardT118_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_19_2 i) (Q2.hfix118_19_2 i) _)
      colCert_118_19_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T118_19
      hfix118_19 hinj118_19 hcardT118_19
      (fun i => conj_mem_of_fixedPoints _ _ (T118_19 i) (hfix118_19 i) _)
      ⟨118, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T118_19_2 Q2.hfix118_19_2 Q2.hinj118_19_2
      Q2.hcardT118_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_19_2 i) (Q2.hfix118_19_2 i) _)
      colCert_118_19_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T118_19
      hfix118_19 hinj118_19 hcardT118_19
      (fun i => conj_mem_of_fixedPoints _ _ (T118_19 i) (hfix118_19 i) _)
      ⟨118, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T118_19_2 Q2.hfix118_19_2 Q2.hinj118_19_2
      Q2.hcardT118_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_19_2 i) (Q2.hfix118_19_2 i) _)
      colCert_118_19_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T118_19
      hfix118_19 hinj118_19 hcardT118_19
      (fun i => conj_mem_of_fixedPoints _ _ (T118_19 i) (hfix118_19 i) _)
      ⟨118, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T118_19_2 Q2.hfix118_19_2 Q2.hinj118_19_2
      Q2.hcardT118_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_19_2 i) (Q2.hfix118_19_2 i) _)
      colCert_118_19_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T118_19
      hfix118_19 hinj118_19 hcardT118_19
      (fun i => conj_mem_of_fixedPoints _ _ (T118_19 i) (hfix118_19 i) _)
      ⟨118, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T118_19_2 Q2.hfix118_19_2 Q2.hinj118_19_2
      Q2.hcardT118_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_19_2 i) (Q2.hfix118_19_2 i) _)
      colCert_118_19_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T118_19
      hfix118_19 hinj118_19 hcardT118_19
      (fun i => conj_mem_of_fixedPoints _ _ (T118_19 i) (hfix118_19 i) _)
      ⟨118, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T118_19_2 Q2.hfix118_19_2 Q2.hinj118_19_2
      Q2.hcardT118_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_19_2 i) (Q2.hfix118_19_2 i) _)
      colCert_118_19_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T118_24
      hfix118_24 hinj118_24 hcardT118_24
      (fun i => conj_mem_of_fixedPoints _ _ (T118_24 i) (hfix118_24 i) _)
      ⟨118, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T118_24_2 Q2.hfix118_24_2 Q2.hinj118_24_2
      Q2.hcardT118_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_24_2 i) (Q2.hfix118_24_2 i) _)
      colCert_118_24_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T118_24
      hfix118_24 hinj118_24 hcardT118_24
      (fun i => conj_mem_of_fixedPoints _ _ (T118_24 i) (hfix118_24 i) _)
      ⟨118, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T118_24_2 Q2.hfix118_24_2 Q2.hinj118_24_2
      Q2.hcardT118_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_24_2 i) (Q2.hfix118_24_2 i) _)
      colCert_118_24_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T118_24
      hfix118_24 hinj118_24 hcardT118_24
      (fun i => conj_mem_of_fixedPoints _ _ (T118_24 i) (hfix118_24 i) _)
      ⟨118, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T118_24_2 Q2.hfix118_24_2 Q2.hinj118_24_2
      Q2.hcardT118_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_24_2 i) (Q2.hfix118_24_2 i) _)
      colCert_118_24_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T118_24
      hfix118_24 hinj118_24 hcardT118_24
      (fun i => conj_mem_of_fixedPoints _ _ (T118_24 i) (hfix118_24 i) _)
      ⟨118, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T118_24_2 Q2.hfix118_24_2 Q2.hinj118_24_2
      Q2.hcardT118_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_24_2 i) (Q2.hfix118_24_2 i) _)
      colCert_118_24_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T118_24
      hfix118_24 hinj118_24 hcardT118_24
      (fun i => conj_mem_of_fixedPoints _ _ (T118_24 i) (hfix118_24 i) _)
      ⟨118, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T118_24_2 Q2.hfix118_24_2 Q2.hinj118_24_2
      Q2.hcardT118_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_24_2 i) (Q2.hfix118_24_2 i) _)
      colCert_118_24_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T118_24
      hfix118_24 hinj118_24 hcardT118_24
      (fun i => conj_mem_of_fixedPoints _ _ (T118_24 i) (hfix118_24 i) _)
      ⟨118, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T118_24_2 Q2.hfix118_24_2 Q2.hinj118_24_2
      Q2.hcardT118_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_24_2 i) (Q2.hfix118_24_2 i) _)
      colCert_118_24_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T118_24
      hfix118_24 hinj118_24 hcardT118_24
      (fun i => conj_mem_of_fixedPoints _ _ (T118_24 i) (hfix118_24 i) _)
      ⟨118, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T118_24_2 Q2.hfix118_24_2 Q2.hinj118_24_2
      Q2.hcardT118_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_24_2 i) (Q2.hfix118_24_2 i) _)
      colCert_118_24_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T118_24
      hfix118_24 hinj118_24 hcardT118_24
      (fun i => conj_mem_of_fixedPoints _ _ (T118_24 i) (hfix118_24 i) _)
      ⟨118, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T118_24_2 Q2.hfix118_24_2 Q2.hinj118_24_2
      Q2.hcardT118_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_24_2 i) (Q2.hfix118_24_2 i) _)
      colCert_118_24_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T118_24
      hfix118_24 hinj118_24 hcardT118_24
      (fun i => conj_mem_of_fixedPoints _ _ (T118_24 i) (hfix118_24 i) _)
      ⟨118, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T118_24_2 Q2.hfix118_24_2 Q2.hinj118_24_2
      Q2.hcardT118_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_24_2 i) (Q2.hfix118_24_2 i) _)
      colCert_118_24_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T118_25
      hfix118_25 hinj118_25 hcardT118_25
      (fun i => conj_mem_of_fixedPoints _ _ (T118_25 i) (hfix118_25 i) _)
      ⟨118, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T118_25_2 Q2.hfix118_25_2 Q2.hinj118_25_2
      Q2.hcardT118_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_25_2 i) (Q2.hfix118_25_2 i) _)
      colCert_118_25_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T118_25
      hfix118_25 hinj118_25 hcardT118_25
      (fun i => conj_mem_of_fixedPoints _ _ (T118_25 i) (hfix118_25 i) _)
      ⟨118, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T118_25_2 Q2.hfix118_25_2 Q2.hinj118_25_2
      Q2.hcardT118_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_25_2 i) (Q2.hfix118_25_2 i) _)
      colCert_118_25_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T118_25
      hfix118_25 hinj118_25 hcardT118_25
      (fun i => conj_mem_of_fixedPoints _ _ (T118_25 i) (hfix118_25 i) _)
      ⟨118, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T118_25_2 Q2.hfix118_25_2 Q2.hinj118_25_2
      Q2.hcardT118_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_25_2 i) (Q2.hfix118_25_2 i) _)
      colCert_118_25_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T118_25
      hfix118_25 hinj118_25 hcardT118_25
      (fun i => conj_mem_of_fixedPoints _ _ (T118_25 i) (hfix118_25 i) _)
      ⟨118, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T118_25_2 Q2.hfix118_25_2 Q2.hinj118_25_2
      Q2.hcardT118_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_25_2 i) (Q2.hfix118_25_2 i) _)
      colCert_118_25_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T118_25
      hfix118_25 hinj118_25 hcardT118_25
      (fun i => conj_mem_of_fixedPoints _ _ (T118_25 i) (hfix118_25 i) _)
      ⟨118, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T118_25_2 Q2.hfix118_25_2 Q2.hinj118_25_2
      Q2.hcardT118_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_25_2 i) (Q2.hfix118_25_2 i) _)
      colCert_118_25_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T118_25
      hfix118_25 hinj118_25 hcardT118_25
      (fun i => conj_mem_of_fixedPoints _ _ (T118_25 i) (hfix118_25 i) _)
      ⟨118, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T118_25_2 Q2.hfix118_25_2 Q2.hinj118_25_2
      Q2.hcardT118_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_25_2 i) (Q2.hfix118_25_2 i) _)
      colCert_118_25_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T118_25
      hfix118_25 hinj118_25 hcardT118_25
      (fun i => conj_mem_of_fixedPoints _ _ (T118_25 i) (hfix118_25 i) _)
      ⟨118, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T118_25_2 Q2.hfix118_25_2 Q2.hinj118_25_2
      Q2.hcardT118_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_25_2 i) (Q2.hfix118_25_2 i) _)
      colCert_118_25_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T118_25
      hfix118_25 hinj118_25 hcardT118_25
      (fun i => conj_mem_of_fixedPoints _ _ (T118_25 i) (hfix118_25 i) _)
      ⟨118, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T118_25_2 Q2.hfix118_25_2 Q2.hinj118_25_2
      Q2.hcardT118_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_25_2 i) (Q2.hfix118_25_2 i) _)
      colCert_118_25_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T118_25
      hfix118_25 hinj118_25 hcardT118_25
      (fun i => conj_mem_of_fixedPoints _ _ (T118_25 i) (hfix118_25 i) _)
      ⟨118, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T118_25_2 Q2.hfix118_25_2 Q2.hinj118_25_2
      Q2.hcardT118_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_25_2 i) (Q2.hfix118_25_2 i) _)
      colCert_118_25_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T118_26
      hfix118_26 hinj118_26 hcardT118_26
      (fun i => conj_mem_of_fixedPoints _ _ (T118_26 i) (hfix118_26 i) _)
      ⟨118, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T118_26_2 Q2.hfix118_26_2 Q2.hinj118_26_2
      Q2.hcardT118_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_26_2 i) (Q2.hfix118_26_2 i) _)
      colCert_118_26_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T118_26
      hfix118_26 hinj118_26 hcardT118_26
      (fun i => conj_mem_of_fixedPoints _ _ (T118_26 i) (hfix118_26 i) _)
      ⟨118, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T118_26_2 Q2.hfix118_26_2 Q2.hinj118_26_2
      Q2.hcardT118_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_26_2 i) (Q2.hfix118_26_2 i) _)
      colCert_118_26_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T118_26
      hfix118_26 hinj118_26 hcardT118_26
      (fun i => conj_mem_of_fixedPoints _ _ (T118_26 i) (hfix118_26 i) _)
      ⟨118, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T118_26_2 Q2.hfix118_26_2 Q2.hinj118_26_2
      Q2.hcardT118_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_26_2 i) (Q2.hfix118_26_2 i) _)
      colCert_118_26_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T118_26
      hfix118_26 hinj118_26 hcardT118_26
      (fun i => conj_mem_of_fixedPoints _ _ (T118_26 i) (hfix118_26 i) _)
      ⟨118, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T118_26_2 Q2.hfix118_26_2 Q2.hinj118_26_2
      Q2.hcardT118_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_26_2 i) (Q2.hfix118_26_2 i) _)
      colCert_118_26_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T118_26
      hfix118_26 hinj118_26 hcardT118_26
      (fun i => conj_mem_of_fixedPoints _ _ (T118_26 i) (hfix118_26 i) _)
      ⟨118, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T118_26_2 Q2.hfix118_26_2 Q2.hinj118_26_2
      Q2.hcardT118_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_26_2 i) (Q2.hfix118_26_2 i) _)
      colCert_118_26_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T118_26
      hfix118_26 hinj118_26 hcardT118_26
      (fun i => conj_mem_of_fixedPoints _ _ (T118_26 i) (hfix118_26 i) _)
      ⟨118, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T118_26_2 Q2.hfix118_26_2 Q2.hinj118_26_2
      Q2.hcardT118_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_26_2 i) (Q2.hfix118_26_2 i) _)
      colCert_118_26_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T118_26
      hfix118_26 hinj118_26 hcardT118_26
      (fun i => conj_mem_of_fixedPoints _ _ (T118_26 i) (hfix118_26 i) _)
      ⟨118, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T118_26_2 Q2.hfix118_26_2 Q2.hinj118_26_2
      Q2.hcardT118_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_26_2 i) (Q2.hfix118_26_2 i) _)
      colCert_118_26_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T118_26
      hfix118_26 hinj118_26 hcardT118_26
      (fun i => conj_mem_of_fixedPoints _ _ (T118_26 i) (hfix118_26 i) _)
      ⟨118, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T118_26_2 Q2.hfix118_26_2 Q2.hinj118_26_2
      Q2.hcardT118_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_26_2 i) (Q2.hfix118_26_2 i) _)
      colCert_118_26_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T118_26
      hfix118_26 hinj118_26 hcardT118_26
      (fun i => conj_mem_of_fixedPoints _ _ (T118_26 i) (hfix118_26 i) _)
      ⟨118, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T118_26_2 Q2.hfix118_26_2 Q2.hinj118_26_2
      Q2.hcardT118_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_26_2 i) (Q2.hfix118_26_2 i) _)
      colCert_118_26_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T118_27
      hfix118_27 hinj118_27 hcardT118_27
      (fun i => conj_mem_of_fixedPoints _ _ (T118_27 i) (hfix118_27 i) _)
      ⟨118, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T118_27_2 Q2.hfix118_27_2 Q2.hinj118_27_2
      Q2.hcardT118_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_27_2 i) (Q2.hfix118_27_2 i) _)
      colCert_118_27_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T118_27
      hfix118_27 hinj118_27 hcardT118_27
      (fun i => conj_mem_of_fixedPoints _ _ (T118_27 i) (hfix118_27 i) _)
      ⟨118, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T118_27_2 Q2.hfix118_27_2 Q2.hinj118_27_2
      Q2.hcardT118_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_27_2 i) (Q2.hfix118_27_2 i) _)
      colCert_118_27_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T118_27
      hfix118_27 hinj118_27 hcardT118_27
      (fun i => conj_mem_of_fixedPoints _ _ (T118_27 i) (hfix118_27 i) _)
      ⟨118, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T118_27_2 Q2.hfix118_27_2 Q2.hinj118_27_2
      Q2.hcardT118_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_27_2 i) (Q2.hfix118_27_2 i) _)
      colCert_118_27_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T118_27
      hfix118_27 hinj118_27 hcardT118_27
      (fun i => conj_mem_of_fixedPoints _ _ (T118_27 i) (hfix118_27 i) _)
      ⟨118, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T118_27_2 Q2.hfix118_27_2 Q2.hinj118_27_2
      Q2.hcardT118_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_27_2 i) (Q2.hfix118_27_2 i) _)
      colCert_118_27_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T118_27
      hfix118_27 hinj118_27 hcardT118_27
      (fun i => conj_mem_of_fixedPoints _ _ (T118_27 i) (hfix118_27 i) _)
      ⟨118, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T118_27_2 Q2.hfix118_27_2 Q2.hinj118_27_2
      Q2.hcardT118_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_27_2 i) (Q2.hfix118_27_2 i) _)
      colCert_118_27_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T118_27
      hfix118_27 hinj118_27 hcardT118_27
      (fun i => conj_mem_of_fixedPoints _ _ (T118_27 i) (hfix118_27 i) _)
      ⟨118, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T118_27_2 Q2.hfix118_27_2 Q2.hinj118_27_2
      Q2.hcardT118_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_27_2 i) (Q2.hfix118_27_2 i) _)
      colCert_118_27_5.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T118_27
      hfix118_27 hinj118_27 hcardT118_27
      (fun i => conj_mem_of_fixedPoints _ _ (T118_27 i) (hfix118_27 i) _)
      ⟨118, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T118_27_2 Q2.hfix118_27_2 Q2.hinj118_27_2
      Q2.hcardT118_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_27_2 i) (Q2.hfix118_27_2 i) _)
      colCert_118_27_10.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T118_27
      hfix118_27 hinj118_27 hcardT118_27
      (fun i => conj_mem_of_fixedPoints _ _ (T118_27 i) (hfix118_27 i) _)
      ⟨118, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T118_27_2 Q2.hfix118_27_2 Q2.hinj118_27_2
      Q2.hcardT118_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_27_2 i) (Q2.hfix118_27_2 i) _)
      colCert_118_27_15.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T118_27
      hfix118_27 hinj118_27 hcardT118_27
      (fun i => conj_mem_of_fixedPoints _ _ (T118_27 i) (hfix118_27 i) _)
      ⟨118, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T118_27_2 Q2.hfix118_27_2 Q2.hinj118_27_2
      Q2.hcardT118_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_27_2 i) (Q2.hfix118_27_2 i) _)
      colCert_118_27_20.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T118_30
      hfix118_30 hinj118_30 hcardT118_30
      (fun i => conj_mem_of_fixedPoints _ _ (T118_30 i) (hfix118_30 i) _)
      ⟨118, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T118_30_2 Q2.hfix118_30_2 Q2.hinj118_30_2
      Q2.hcardT118_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_30_2 i) (Q2.hfix118_30_2 i) _)
      colCert_118_30_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T118_30
      hfix118_30 hinj118_30 hcardT118_30
      (fun i => conj_mem_of_fixedPoints _ _ (T118_30 i) (hfix118_30 i) _)
      ⟨118, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T118_30_2 Q2.hfix118_30_2 Q2.hinj118_30_2
      Q2.hcardT118_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_30_2 i) (Q2.hfix118_30_2 i) _)
      colCert_118_30_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T118_30
      hfix118_30 hinj118_30 hcardT118_30
      (fun i => conj_mem_of_fixedPoints _ _ (T118_30 i) (hfix118_30 i) _)
      ⟨118, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T118_30_2 Q2.hfix118_30_2 Q2.hinj118_30_2
      Q2.hcardT118_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_30_2 i) (Q2.hfix118_30_2 i) _)
      colCert_118_30_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T118_30
      hfix118_30 hinj118_30 hcardT118_30
      (fun i => conj_mem_of_fixedPoints _ _ (T118_30 i) (hfix118_30 i) _)
      ⟨118, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T118_30_2 Q2.hfix118_30_2 Q2.hinj118_30_2
      Q2.hcardT118_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_30_2 i) (Q2.hfix118_30_2 i) _)
      colCert_118_30_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T118_30
      hfix118_30 hinj118_30 hcardT118_30
      (fun i => conj_mem_of_fixedPoints _ _ (T118_30 i) (hfix118_30 i) _)
      ⟨118, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T118_30_2 Q2.hfix118_30_2 Q2.hinj118_30_2
      Q2.hcardT118_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_30_2 i) (Q2.hfix118_30_2 i) _)
      colCert_118_30_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T118_30
      hfix118_30 hinj118_30 hcardT118_30
      (fun i => conj_mem_of_fixedPoints _ _ (T118_30 i) (hfix118_30 i) _)
      ⟨118, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T118_30_2 Q2.hfix118_30_2 Q2.hinj118_30_2
      Q2.hcardT118_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_30_2 i) (Q2.hfix118_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T118_30 = colFn colCertDiv_118_30_5.D1 (m := 5) from colCertDiv_118_30_5.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T118_30_2 = colFn colCertDiv_118_30_5.D2 (m := 5) from colCertDiv_118_30_5.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_30_5_match


theorem leaf_118_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T118_30
      hfix118_30 hinj118_30 hcardT118_30
      (fun i => conj_mem_of_fixedPoints _ _ (T118_30 i) (hfix118_30 i) _)
      ⟨118, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T118_30_2 Q2.hfix118_30_2 Q2.hinj118_30_2
      Q2.hcardT118_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_30_2 i) (Q2.hfix118_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T118_30 = colFn colCertDiv_118_30_10.D1 (m := 5) from colCertDiv_118_30_10.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T118_30_2 = colFn colCertDiv_118_30_10.D2 (m := 5) from colCertDiv_118_30_10.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_30_10_match


theorem leaf_118_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T118_30
      hfix118_30 hinj118_30 hcardT118_30
      (fun i => conj_mem_of_fixedPoints _ _ (T118_30 i) (hfix118_30 i) _)
      ⟨118, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T118_30_2 Q2.hfix118_30_2 Q2.hinj118_30_2
      Q2.hcardT118_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_30_2 i) (Q2.hfix118_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T118_30 = colFn colCertDiv_118_30_15.D1 (m := 5) from colCertDiv_118_30_15.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 15 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T118_30_2 = colFn colCertDiv_118_30_15.D2 (m := 5) from colCertDiv_118_30_15.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_30_15_match


theorem leaf_118_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T118_30
      hfix118_30 hinj118_30 hcardT118_30
      (fun i => conj_mem_of_fixedPoints _ _ (T118_30 i) (hfix118_30 i) _)
      ⟨118, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T118_30_2 Q2.hfix118_30_2 Q2.hinj118_30_2
      Q2.hcardT118_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_30_2 i) (Q2.hfix118_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T118_30 = colFn colCertDiv_118_30_20.D1 (m := 5) from colCertDiv_118_30_20.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 20 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T118_30_2 = colFn colCertDiv_118_30_20.D2 (m := 5) from colCertDiv_118_30_20.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_30_20_match


theorem leaf_118_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T118_35
      hfix118_35 hinj118_35 hcardT118_35
      (fun i => conj_mem_of_fixedPoints _ _ (T118_35 i) (hfix118_35 i) _)
      ⟨118, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T118_35_2 Q2.hfix118_35_2 Q2.hinj118_35_2
      Q2.hcardT118_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_35_2 i) (Q2.hfix118_35_2 i) _)
      colCert_118_35_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T118_35
      hfix118_35 hinj118_35 hcardT118_35
      (fun i => conj_mem_of_fixedPoints _ _ (T118_35 i) (hfix118_35 i) _)
      ⟨118, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T118_35_2 Q2.hfix118_35_2 Q2.hinj118_35_2
      Q2.hcardT118_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_35_2 i) (Q2.hfix118_35_2 i) _)
      colCert_118_35_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T118_35
      hfix118_35 hinj118_35 hcardT118_35
      (fun i => conj_mem_of_fixedPoints _ _ (T118_35 i) (hfix118_35 i) _)
      ⟨118, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T118_35_2 Q2.hfix118_35_2 Q2.hinj118_35_2
      Q2.hcardT118_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_35_2 i) (Q2.hfix118_35_2 i) _)
      colCert_118_35_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T118_35
      hfix118_35 hinj118_35 hcardT118_35
      (fun i => conj_mem_of_fixedPoints _ _ (T118_35 i) (hfix118_35 i) _)
      ⟨118, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T118_35_2 Q2.hfix118_35_2 Q2.hinj118_35_2
      Q2.hcardT118_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_35_2 i) (Q2.hfix118_35_2 i) _)
      colCert_118_35_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T118_35
      hfix118_35 hinj118_35 hcardT118_35
      (fun i => conj_mem_of_fixedPoints _ _ (T118_35 i) (hfix118_35 i) _)
      ⟨118, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T118_35_2 Q2.hfix118_35_2 Q2.hinj118_35_2
      Q2.hcardT118_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_35_2 i) (Q2.hfix118_35_2 i) _)
      colCert_118_35_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T118_35
      hfix118_35 hinj118_35 hcardT118_35
      (fun i => conj_mem_of_fixedPoints _ _ (T118_35 i) (hfix118_35 i) _)
      ⟨118, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T118_35_2 Q2.hfix118_35_2 Q2.hinj118_35_2
      Q2.hcardT118_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_35_2 i) (Q2.hfix118_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T118_35 = colFn colCertDiv_118_35_5.D1 (m := 5) from colCertDiv_118_35_5.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 5 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T118_35_2 = colFn colCertDiv_118_35_5.D2 (m := 5) from colCertDiv_118_35_5.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_35_5_match


theorem leaf_118_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T118_35
      hfix118_35 hinj118_35 hcardT118_35
      (fun i => conj_mem_of_fixedPoints _ _ (T118_35 i) (hfix118_35 i) _)
      ⟨118, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T118_35_2 Q2.hfix118_35_2 Q2.hinj118_35_2
      Q2.hcardT118_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_35_2 i) (Q2.hfix118_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T118_35 = colFn colCertDiv_118_35_10.D1 (m := 5) from colCertDiv_118_35_10.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 10 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T118_35_2 = colFn colCertDiv_118_35_10.D2 (m := 5) from colCertDiv_118_35_10.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_35_10_match


theorem leaf_118_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T118_35
      hfix118_35 hinj118_35 hcardT118_35
      (fun i => conj_mem_of_fixedPoints _ _ (T118_35 i) (hfix118_35 i) _)
      ⟨118, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T118_35_2 Q2.hfix118_35_2 Q2.hinj118_35_2
      Q2.hcardT118_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_35_2 i) (Q2.hfix118_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T118_35 = colFn colCertDiv_118_35_15.D1 (m := 5) from colCertDiv_118_35_15.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T118_35_2 = colFn colCertDiv_118_35_15.D2 (m := 5) from colCertDiv_118_35_15.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_35_15_match


theorem leaf_118_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T118_35
      hfix118_35 hinj118_35 hcardT118_35
      (fun i => conj_mem_of_fixedPoints _ _ (T118_35 i) (hfix118_35 i) _)
      ⟨118, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T118_35_2 Q2.hfix118_35_2 Q2.hinj118_35_2
      Q2.hcardT118_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_35_2 i) (Q2.hfix118_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T118_35 = colFn colCertDiv_118_35_20.D1 (m := 5) from colCertDiv_118_35_20.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T118_35_2 = colFn colCertDiv_118_35_20.D2 (m := 5) from colCertDiv_118_35_20.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_35_20_match


theorem leaf_118_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T118_40
      hfix118_40 hinj118_40 hcardT118_40
      (fun i => conj_mem_of_fixedPoints _ _ (T118_40 i) (hfix118_40 i) _)
      ⟨118, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T118_40_2 Q2.hfix118_40_2 Q2.hinj118_40_2
      Q2.hcardT118_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_40_2 i) (Q2.hfix118_40_2 i) _)
      colCert_118_40_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T118_40
      hfix118_40 hinj118_40 hcardT118_40
      (fun i => conj_mem_of_fixedPoints _ _ (T118_40 i) (hfix118_40 i) _)
      ⟨118, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T118_40_2 Q2.hfix118_40_2 Q2.hinj118_40_2
      Q2.hcardT118_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_40_2 i) (Q2.hfix118_40_2 i) _)
      colCert_118_40_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T118_40
      hfix118_40 hinj118_40 hcardT118_40
      (fun i => conj_mem_of_fixedPoints _ _ (T118_40 i) (hfix118_40 i) _)
      ⟨118, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T118_40_2 Q2.hfix118_40_2 Q2.hinj118_40_2
      Q2.hcardT118_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_40_2 i) (Q2.hfix118_40_2 i) _)
      colCert_118_40_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T118_40
      hfix118_40 hinj118_40 hcardT118_40
      (fun i => conj_mem_of_fixedPoints _ _ (T118_40 i) (hfix118_40 i) _)
      ⟨118, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T118_40_2 Q2.hfix118_40_2 Q2.hinj118_40_2
      Q2.hcardT118_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_40_2 i) (Q2.hfix118_40_2 i) _)
      colCert_118_40_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T118_40
      hfix118_40 hinj118_40 hcardT118_40
      (fun i => conj_mem_of_fixedPoints _ _ (T118_40 i) (hfix118_40 i) _)
      ⟨118, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T118_40_2 Q2.hfix118_40_2 Q2.hinj118_40_2
      Q2.hcardT118_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_40_2 i) (Q2.hfix118_40_2 i) _)
      colCert_118_40_4.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T118_40
      hfix118_40 hinj118_40 hcardT118_40
      (fun i => conj_mem_of_fixedPoints _ _ (T118_40 i) (hfix118_40 i) _)
      ⟨118, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T118_40_2 Q2.hfix118_40_2 Q2.hinj118_40_2
      Q2.hcardT118_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_40_2 i) (Q2.hfix118_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T118_40 = colFn colCertDiv_118_40_5.D1 (m := 5) from colCertDiv_118_40_5.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 5 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T118_40_2 = colFn colCertDiv_118_40_5.D2 (m := 5) from colCertDiv_118_40_5.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_40_5_match


theorem leaf_118_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T118_40
      hfix118_40 hinj118_40 hcardT118_40
      (fun i => conj_mem_of_fixedPoints _ _ (T118_40 i) (hfix118_40 i) _)
      ⟨118, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T118_40_2 Q2.hfix118_40_2 Q2.hinj118_40_2
      Q2.hcardT118_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_40_2 i) (Q2.hfix118_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T118_40 = colFn colCertDiv_118_40_10.D1 (m := 5) from colCertDiv_118_40_10.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 10 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T118_40_2 = colFn colCertDiv_118_40_10.D2 (m := 5) from colCertDiv_118_40_10.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_40_10_match


theorem leaf_118_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T118_40
      hfix118_40 hinj118_40 hcardT118_40
      (fun i => conj_mem_of_fixedPoints _ _ (T118_40 i) (hfix118_40 i) _)
      ⟨118, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T118_40_2 Q2.hfix118_40_2 Q2.hinj118_40_2
      Q2.hcardT118_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_40_2 i) (Q2.hfix118_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T118_40 = colFn colCertDiv_118_40_15.D1 (m := 5) from colCertDiv_118_40_15.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T118_40_2 = colFn colCertDiv_118_40_15.D2 (m := 5) from colCertDiv_118_40_15.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_40_15_match


theorem leaf_118_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨118, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T118_40
      hfix118_40 hinj118_40 hcardT118_40
      (fun i => conj_mem_of_fixedPoints _ _ (T118_40 i) (hfix118_40 i) _)
      ⟨118, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T118_40_2 Q2.hfix118_40_2 Q2.hinj118_40_2
      Q2.hcardT118_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_40_2 i) (Q2.hfix118_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨118, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T118_40 = colFn colCertDiv_118_40_20.D1 (m := 5) from colCertDiv_118_40_20.bind1,
    show colData2 (⟨118, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T118_40_2 = colFn colCertDiv_118_40_20.D2 (m := 5) from colCertDiv_118_40_20.bind2]
  rw [alnId_118 j hj]
  exact fastcode_of_div ⟨118, by decide⟩ _ _ _
    ((alnId_118 j hj) ▸ Q2.listedAt (⟨118, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨118, by decide⟩ : Fin 148) hj hq).1) colCertDiv_118_40_20_match


theorem leaf_118_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T118_45
      hfix118_45 hinj118_45 hcardT118_45
      (fun i => conj_mem_of_fixedPoints _ _ (T118_45 i) (hfix118_45 i) _)
      ⟨118, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T118_45_2 Q2.hfix118_45_2 Q2.hinj118_45_2
      Q2.hcardT118_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_45_2 i) (Q2.hfix118_45_2 i) _)
      colCert_118_45_0.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T118_45
      hfix118_45 hinj118_45 hcardT118_45
      (fun i => conj_mem_of_fixedPoints _ _ (T118_45 i) (hfix118_45 i) _)
      ⟨118, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T118_45_2 Q2.hfix118_45_2 Q2.hinj118_45_2
      Q2.hcardT118_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_45_2 i) (Q2.hfix118_45_2 i) _)
      colCert_118_45_1.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T118_45
      hfix118_45 hinj118_45 hcardT118_45
      (fun i => conj_mem_of_fixedPoints _ _ (T118_45 i) (hfix118_45 i) _)
      ⟨118, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T118_45_2 Q2.hfix118_45_2 Q2.hinj118_45_2
      Q2.hcardT118_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_45_2 i) (Q2.hfix118_45_2 i) _)
      colCert_118_45_2.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T118_45
      hfix118_45 hinj118_45 hcardT118_45
      (fun i => conj_mem_of_fixedPoints _ _ (T118_45 i) (hfix118_45 i) _)
      ⟨118, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T118_45_2 Q2.hfix118_45_2 Q2.hinj118_45_2
      Q2.hcardT118_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_45_2 i) (Q2.hfix118_45_2 i) _)
      colCert_118_45_3.hD ?_).symm
  rw [alnId_118 j hj]


theorem leaf_118_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 118 []).length)
    (hq : (normIsRep.getD 118 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨118, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨118, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨118, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨118, by decide⟩ (listedAt ⟨118, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T118_45
      hfix118_45 hinj118_45 hcardT118_45
      (fun i => conj_mem_of_fixedPoints _ _ (T118_45 i) (hfix118_45 i) _)
      ⟨118, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨118, by decide⟩ (Q2.listedAt ⟨118, by decide⟩
        (alnCheck_rep ⟨118, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T118_45_2 Q2.hfix118_45_2 Q2.hinj118_45_2
      Q2.hcardT118_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T118_45_2 i) (Q2.hfix118_45_2 i) _)
      colCert_118_45_4.hD ?_).symm
  rw [alnId_118 j hj]


end LeanDring.P5Presentation
