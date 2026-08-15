/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C003
import LeanDring.P5.Data.ColRestCheap.C024
import LeanDring.P5.Data.ColRestCheap.C025
import LeanDring.P5.Data.ColRestCheap.C026
import LeanDring.P5.Data.ColRestCheap.C027
import LeanDring.P5.Data.ColRestCheap.C028
import LeanDring.P5.Data.EntryK.C026
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C032

/-! # Stage-5 leaves, chunk 23 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_117_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T117_19
      hfix117_19 hinj117_19 hcardT117_19
      (fun i => conj_mem_of_fixedPoints _ _ (T117_19 i) (hfix117_19 i) _)
      ⟨117, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T117_19_2 Q2.hfix117_19_2 Q2.hinj117_19_2
      Q2.hcardT117_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_19_2 i) (Q2.hfix117_19_2 i) _)
      colCert_117_19_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T117_19
      hfix117_19 hinj117_19 hcardT117_19
      (fun i => conj_mem_of_fixedPoints _ _ (T117_19 i) (hfix117_19 i) _)
      ⟨117, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T117_19_2 Q2.hfix117_19_2 Q2.hinj117_19_2
      Q2.hcardT117_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_19_2 i) (Q2.hfix117_19_2 i) _)
      colCert_117_19_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T117_19
      hfix117_19 hinj117_19 hcardT117_19
      (fun i => conj_mem_of_fixedPoints _ _ (T117_19 i) (hfix117_19 i) _)
      ⟨117, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T117_19_2 Q2.hfix117_19_2 Q2.hinj117_19_2
      Q2.hcardT117_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_19_2 i) (Q2.hfix117_19_2 i) _)
      colCert_117_19_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T117_19
      hfix117_19 hinj117_19 hcardT117_19
      (fun i => conj_mem_of_fixedPoints _ _ (T117_19 i) (hfix117_19 i) _)
      ⟨117, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T117_19_2 Q2.hfix117_19_2 Q2.hinj117_19_2
      Q2.hcardT117_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_19_2 i) (Q2.hfix117_19_2 i) _)
      colCert_117_19_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T117_19
      hfix117_19 hinj117_19 hcardT117_19
      (fun i => conj_mem_of_fixedPoints _ _ (T117_19 i) (hfix117_19 i) _)
      ⟨117, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T117_19_2 Q2.hfix117_19_2 Q2.hinj117_19_2
      Q2.hcardT117_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_19_2 i) (Q2.hfix117_19_2 i) _)
      colCert_117_19_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T117_19
      hfix117_19 hinj117_19 hcardT117_19
      (fun i => conj_mem_of_fixedPoints _ _ (T117_19 i) (hfix117_19 i) _)
      ⟨117, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T117_19_2 Q2.hfix117_19_2 Q2.hinj117_19_2
      Q2.hcardT117_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_19_2 i) (Q2.hfix117_19_2 i) _)
      colCert_117_19_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T117_19
      hfix117_19 hinj117_19 hcardT117_19
      (fun i => conj_mem_of_fixedPoints _ _ (T117_19 i) (hfix117_19 i) _)
      ⟨117, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T117_19_2 Q2.hfix117_19_2 Q2.hinj117_19_2
      Q2.hcardT117_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_19_2 i) (Q2.hfix117_19_2 i) _)
      colCert_117_19_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T117_19
      hfix117_19 hinj117_19 hcardT117_19
      (fun i => conj_mem_of_fixedPoints _ _ (T117_19 i) (hfix117_19 i) _)
      ⟨117, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T117_19_2 Q2.hfix117_19_2 Q2.hinj117_19_2
      Q2.hcardT117_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_19_2 i) (Q2.hfix117_19_2 i) _)
      colCert_117_19_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T117_19
      hfix117_19 hinj117_19 hcardT117_19
      (fun i => conj_mem_of_fixedPoints _ _ (T117_19 i) (hfix117_19 i) _)
      ⟨117, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T117_19_2 Q2.hfix117_19_2 Q2.hinj117_19_2
      Q2.hcardT117_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_19_2 i) (Q2.hfix117_19_2 i) _)
      colCert_117_19_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T117_24
      hfix117_24 hinj117_24 hcardT117_24
      (fun i => conj_mem_of_fixedPoints _ _ (T117_24 i) (hfix117_24 i) _)
      ⟨117, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T117_24_2 Q2.hfix117_24_2 Q2.hinj117_24_2
      Q2.hcardT117_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_24_2 i) (Q2.hfix117_24_2 i) _)
      colCert_117_24_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T117_24
      hfix117_24 hinj117_24 hcardT117_24
      (fun i => conj_mem_of_fixedPoints _ _ (T117_24 i) (hfix117_24 i) _)
      ⟨117, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T117_24_2 Q2.hfix117_24_2 Q2.hinj117_24_2
      Q2.hcardT117_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_24_2 i) (Q2.hfix117_24_2 i) _)
      colCert_117_24_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T117_24
      hfix117_24 hinj117_24 hcardT117_24
      (fun i => conj_mem_of_fixedPoints _ _ (T117_24 i) (hfix117_24 i) _)
      ⟨117, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T117_24_2 Q2.hfix117_24_2 Q2.hinj117_24_2
      Q2.hcardT117_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_24_2 i) (Q2.hfix117_24_2 i) _)
      colCert_117_24_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T117_24
      hfix117_24 hinj117_24 hcardT117_24
      (fun i => conj_mem_of_fixedPoints _ _ (T117_24 i) (hfix117_24 i) _)
      ⟨117, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T117_24_2 Q2.hfix117_24_2 Q2.hinj117_24_2
      Q2.hcardT117_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_24_2 i) (Q2.hfix117_24_2 i) _)
      colCert_117_24_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T117_24
      hfix117_24 hinj117_24 hcardT117_24
      (fun i => conj_mem_of_fixedPoints _ _ (T117_24 i) (hfix117_24 i) _)
      ⟨117, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T117_24_2 Q2.hfix117_24_2 Q2.hinj117_24_2
      Q2.hcardT117_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_24_2 i) (Q2.hfix117_24_2 i) _)
      colCert_117_24_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T117_24
      hfix117_24 hinj117_24 hcardT117_24
      (fun i => conj_mem_of_fixedPoints _ _ (T117_24 i) (hfix117_24 i) _)
      ⟨117, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T117_24_2 Q2.hfix117_24_2 Q2.hinj117_24_2
      Q2.hcardT117_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_24_2 i) (Q2.hfix117_24_2 i) _)
      colCert_117_24_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T117_24
      hfix117_24 hinj117_24 hcardT117_24
      (fun i => conj_mem_of_fixedPoints _ _ (T117_24 i) (hfix117_24 i) _)
      ⟨117, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T117_24_2 Q2.hfix117_24_2 Q2.hinj117_24_2
      Q2.hcardT117_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_24_2 i) (Q2.hfix117_24_2 i) _)
      colCert_117_24_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T117_24
      hfix117_24 hinj117_24 hcardT117_24
      (fun i => conj_mem_of_fixedPoints _ _ (T117_24 i) (hfix117_24 i) _)
      ⟨117, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T117_24_2 Q2.hfix117_24_2 Q2.hinj117_24_2
      Q2.hcardT117_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_24_2 i) (Q2.hfix117_24_2 i) _)
      colCert_117_24_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T117_24
      hfix117_24 hinj117_24 hcardT117_24
      (fun i => conj_mem_of_fixedPoints _ _ (T117_24 i) (hfix117_24 i) _)
      ⟨117, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T117_24_2 Q2.hfix117_24_2 Q2.hinj117_24_2
      Q2.hcardT117_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_24_2 i) (Q2.hfix117_24_2 i) _)
      colCert_117_24_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T117_25
      hfix117_25 hinj117_25 hcardT117_25
      (fun i => conj_mem_of_fixedPoints _ _ (T117_25 i) (hfix117_25 i) _)
      ⟨117, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T117_25_2 Q2.hfix117_25_2 Q2.hinj117_25_2
      Q2.hcardT117_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_25_2 i) (Q2.hfix117_25_2 i) _)
      colCert_117_25_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T117_25
      hfix117_25 hinj117_25 hcardT117_25
      (fun i => conj_mem_of_fixedPoints _ _ (T117_25 i) (hfix117_25 i) _)
      ⟨117, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T117_25_2 Q2.hfix117_25_2 Q2.hinj117_25_2
      Q2.hcardT117_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_25_2 i) (Q2.hfix117_25_2 i) _)
      colCert_117_25_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T117_25
      hfix117_25 hinj117_25 hcardT117_25
      (fun i => conj_mem_of_fixedPoints _ _ (T117_25 i) (hfix117_25 i) _)
      ⟨117, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T117_25_2 Q2.hfix117_25_2 Q2.hinj117_25_2
      Q2.hcardT117_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_25_2 i) (Q2.hfix117_25_2 i) _)
      colCert_117_25_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T117_25
      hfix117_25 hinj117_25 hcardT117_25
      (fun i => conj_mem_of_fixedPoints _ _ (T117_25 i) (hfix117_25 i) _)
      ⟨117, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T117_25_2 Q2.hfix117_25_2 Q2.hinj117_25_2
      Q2.hcardT117_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_25_2 i) (Q2.hfix117_25_2 i) _)
      colCert_117_25_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T117_25
      hfix117_25 hinj117_25 hcardT117_25
      (fun i => conj_mem_of_fixedPoints _ _ (T117_25 i) (hfix117_25 i) _)
      ⟨117, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T117_25_2 Q2.hfix117_25_2 Q2.hinj117_25_2
      Q2.hcardT117_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_25_2 i) (Q2.hfix117_25_2 i) _)
      colCert_117_25_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T117_25
      hfix117_25 hinj117_25 hcardT117_25
      (fun i => conj_mem_of_fixedPoints _ _ (T117_25 i) (hfix117_25 i) _)
      ⟨117, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T117_25_2 Q2.hfix117_25_2 Q2.hinj117_25_2
      Q2.hcardT117_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_25_2 i) (Q2.hfix117_25_2 i) _)
      colCert_117_25_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T117_25
      hfix117_25 hinj117_25 hcardT117_25
      (fun i => conj_mem_of_fixedPoints _ _ (T117_25 i) (hfix117_25 i) _)
      ⟨117, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T117_25_2 Q2.hfix117_25_2 Q2.hinj117_25_2
      Q2.hcardT117_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_25_2 i) (Q2.hfix117_25_2 i) _)
      colCert_117_25_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T117_25
      hfix117_25 hinj117_25 hcardT117_25
      (fun i => conj_mem_of_fixedPoints _ _ (T117_25 i) (hfix117_25 i) _)
      ⟨117, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T117_25_2 Q2.hfix117_25_2 Q2.hinj117_25_2
      Q2.hcardT117_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_25_2 i) (Q2.hfix117_25_2 i) _)
      colCert_117_25_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T117_25
      hfix117_25 hinj117_25 hcardT117_25
      (fun i => conj_mem_of_fixedPoints _ _ (T117_25 i) (hfix117_25 i) _)
      ⟨117, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T117_25_2 Q2.hfix117_25_2 Q2.hinj117_25_2
      Q2.hcardT117_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_25_2 i) (Q2.hfix117_25_2 i) _)
      colCert_117_25_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T117_26
      hfix117_26 hinj117_26 hcardT117_26
      (fun i => conj_mem_of_fixedPoints _ _ (T117_26 i) (hfix117_26 i) _)
      ⟨117, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T117_26_2 Q2.hfix117_26_2 Q2.hinj117_26_2
      Q2.hcardT117_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_26_2 i) (Q2.hfix117_26_2 i) _)
      colCert_117_26_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T117_26
      hfix117_26 hinj117_26 hcardT117_26
      (fun i => conj_mem_of_fixedPoints _ _ (T117_26 i) (hfix117_26 i) _)
      ⟨117, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T117_26_2 Q2.hfix117_26_2 Q2.hinj117_26_2
      Q2.hcardT117_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_26_2 i) (Q2.hfix117_26_2 i) _)
      colCert_117_26_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T117_26
      hfix117_26 hinj117_26 hcardT117_26
      (fun i => conj_mem_of_fixedPoints _ _ (T117_26 i) (hfix117_26 i) _)
      ⟨117, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T117_26_2 Q2.hfix117_26_2 Q2.hinj117_26_2
      Q2.hcardT117_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_26_2 i) (Q2.hfix117_26_2 i) _)
      colCert_117_26_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T117_26
      hfix117_26 hinj117_26 hcardT117_26
      (fun i => conj_mem_of_fixedPoints _ _ (T117_26 i) (hfix117_26 i) _)
      ⟨117, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T117_26_2 Q2.hfix117_26_2 Q2.hinj117_26_2
      Q2.hcardT117_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_26_2 i) (Q2.hfix117_26_2 i) _)
      colCert_117_26_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T117_26
      hfix117_26 hinj117_26 hcardT117_26
      (fun i => conj_mem_of_fixedPoints _ _ (T117_26 i) (hfix117_26 i) _)
      ⟨117, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T117_26_2 Q2.hfix117_26_2 Q2.hinj117_26_2
      Q2.hcardT117_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_26_2 i) (Q2.hfix117_26_2 i) _)
      colCert_117_26_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_26_5 (hp : 5 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 5 (transLenTr ⟨26, by decide⟩ 5 hp)) T117_26
      hfix117_26 hinj117_26 hcardT117_26
      (fun i => conj_mem_of_fixedPoints _ _ (T117_26 i) (hfix117_26 i) _)
      ⟨117, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 5 hp) Q2.T117_26_2 Q2.hfix117_26_2 Q2.hinj117_26_2
      Q2.hcardT117_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_26_2 i) (Q2.hfix117_26_2 i) _)
      colCert_117_26_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_26_10 (hp : 10 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 10 (transLenTr ⟨26, by decide⟩ 10 hp)) T117_26
      hfix117_26 hinj117_26 hcardT117_26
      (fun i => conj_mem_of_fixedPoints _ _ (T117_26 i) (hfix117_26 i) _)
      ⟨117, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 10 hp) Q2.T117_26_2 Q2.hfix117_26_2 Q2.hinj117_26_2
      Q2.hcardT117_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_26_2 i) (Q2.hfix117_26_2 i) _)
      colCert_117_26_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_26_15 (hp : 15 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 15 (transLenTr ⟨26, by decide⟩ 15 hp)) T117_26
      hfix117_26 hinj117_26 hcardT117_26
      (fun i => conj_mem_of_fixedPoints _ _ (T117_26 i) (hfix117_26 i) _)
      ⟨117, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 15 hp) Q2.T117_26_2 Q2.hfix117_26_2 Q2.hinj117_26_2
      Q2.hcardT117_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_26_2 i) (Q2.hfix117_26_2 i) _)
      colCert_117_26_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_26_20 (hp : 20 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 20 (transLenTr ⟨26, by decide⟩ 20 hp)) T117_26
      hfix117_26 hinj117_26 hcardT117_26
      (fun i => conj_mem_of_fixedPoints _ _ (T117_26 i) (hfix117_26 i) _)
      ⟨117, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 20 hp) Q2.T117_26_2 Q2.hfix117_26_2 Q2.hinj117_26_2
      Q2.hcardT117_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_26_2 i) (Q2.hfix117_26_2 i) _)
      colCert_117_26_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_27_0 (hp : 0 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 0 (transLenTr ⟨27, by decide⟩ 0 hp)) T117_27
      hfix117_27 hinj117_27 hcardT117_27
      (fun i => conj_mem_of_fixedPoints _ _ (T117_27 i) (hfix117_27 i) _)
      ⟨117, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 0 hp) Q2.T117_27_2 Q2.hfix117_27_2 Q2.hinj117_27_2
      Q2.hcardT117_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_27_2 i) (Q2.hfix117_27_2 i) _)
      colCert_117_27_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_27_1 (hp : 1 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 1 (transLenTr ⟨27, by decide⟩ 1 hp)) T117_27
      hfix117_27 hinj117_27 hcardT117_27
      (fun i => conj_mem_of_fixedPoints _ _ (T117_27 i) (hfix117_27 i) _)
      ⟨117, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 1 hp) Q2.T117_27_2 Q2.hfix117_27_2 Q2.hinj117_27_2
      Q2.hcardT117_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_27_2 i) (Q2.hfix117_27_2 i) _)
      colCert_117_27_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_27_2 (hp : 2 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 2 (transLenTr ⟨27, by decide⟩ 2 hp)) T117_27
      hfix117_27 hinj117_27 hcardT117_27
      (fun i => conj_mem_of_fixedPoints _ _ (T117_27 i) (hfix117_27 i) _)
      ⟨117, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 2 hp) Q2.T117_27_2 Q2.hfix117_27_2 Q2.hinj117_27_2
      Q2.hcardT117_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_27_2 i) (Q2.hfix117_27_2 i) _)
      colCert_117_27_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_27_3 (hp : 3 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 3 (transLenTr ⟨27, by decide⟩ 3 hp)) T117_27
      hfix117_27 hinj117_27 hcardT117_27
      (fun i => conj_mem_of_fixedPoints _ _ (T117_27 i) (hfix117_27 i) _)
      ⟨117, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 3 hp) Q2.T117_27_2 Q2.hfix117_27_2 Q2.hinj117_27_2
      Q2.hcardT117_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_27_2 i) (Q2.hfix117_27_2 i) _)
      colCert_117_27_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_27_4 (hp : 4 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 4 (transLenTr ⟨27, by decide⟩ 4 hp)) T117_27
      hfix117_27 hinj117_27 hcardT117_27
      (fun i => conj_mem_of_fixedPoints _ _ (T117_27 i) (hfix117_27 i) _)
      ⟨117, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 4 hp) Q2.T117_27_2 Q2.hfix117_27_2 Q2.hinj117_27_2
      Q2.hcardT117_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_27_2 i) (Q2.hfix117_27_2 i) _)
      colCert_117_27_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_27_5 (hp : 5 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 5 (transLenTr ⟨27, by decide⟩ 5 hp)) T117_27
      hfix117_27 hinj117_27 hcardT117_27
      (fun i => conj_mem_of_fixedPoints _ _ (T117_27 i) (hfix117_27 i) _)
      ⟨117, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 5 hp) Q2.T117_27_2 Q2.hfix117_27_2 Q2.hinj117_27_2
      Q2.hcardT117_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_27_2 i) (Q2.hfix117_27_2 i) _)
      colCert_117_27_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_27_10 (hp : 10 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 10 (transLenTr ⟨27, by decide⟩ 10 hp)) T117_27
      hfix117_27 hinj117_27 hcardT117_27
      (fun i => conj_mem_of_fixedPoints _ _ (T117_27 i) (hfix117_27 i) _)
      ⟨117, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 10 hp) Q2.T117_27_2 Q2.hfix117_27_2 Q2.hinj117_27_2
      Q2.hcardT117_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_27_2 i) (Q2.hfix117_27_2 i) _)
      colCert_117_27_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_27_15 (hp : 15 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 15 (transLenTr ⟨27, by decide⟩ 15 hp)) T117_27
      hfix117_27 hinj117_27 hcardT117_27
      (fun i => conj_mem_of_fixedPoints _ _ (T117_27 i) (hfix117_27 i) _)
      ⟨117, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 15 hp) Q2.T117_27_2 Q2.hfix117_27_2 Q2.hinj117_27_2
      Q2.hcardT117_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_27_2 i) (Q2.hfix117_27_2 i) _)
      colCert_117_27_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_27_20 (hp : 20 < (Q2.transData.getD 27 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨27, by decide⟩ : Fin 148)) (colE2 ⟨27, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨27, by decide⟩ : Fin 148))
        (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨27, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨27, by decide⟩ 20 (transLenTr ⟨27, by decide⟩ 20 hp)) T117_27
      hfix117_27 hinj117_27 hcardT117_27
      (fun i => conj_mem_of_fixedPoints _ _ (T117_27 i) (hfix117_27 i) _)
      ⟨117, by decide⟩ ⟨27, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨27, by decide⟩ 20 hp) Q2.T117_27_2 Q2.hfix117_27_2 Q2.hinj117_27_2
      Q2.hcardT117_27_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_27_2 i) (Q2.hfix117_27_2 i) _)
      colCert_117_27_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_29_0 (hp : 0 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 0 (transLenTr ⟨29, by decide⟩ 0 hp)) T117_29
      hfix117_29 hinj117_29 hcardT117_29
      (fun i => conj_mem_of_fixedPoints _ _ (T117_29 i) (hfix117_29 i) _)
      ⟨117, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 0 hp) Q2.T117_29_2 Q2.hfix117_29_2 Q2.hinj117_29_2
      Q2.hcardT117_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_29_2 i) (Q2.hfix117_29_2 i) _)
      colCert_117_29_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_29_1 (hp : 1 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 1 (transLenTr ⟨29, by decide⟩ 1 hp)) T117_29
      hfix117_29 hinj117_29 hcardT117_29
      (fun i => conj_mem_of_fixedPoints _ _ (T117_29 i) (hfix117_29 i) _)
      ⟨117, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 1 hp) Q2.T117_29_2 Q2.hfix117_29_2 Q2.hinj117_29_2
      Q2.hcardT117_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_29_2 i) (Q2.hfix117_29_2 i) _)
      colCert_117_29_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_29_2 (hp : 2 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 2 (transLenTr ⟨29, by decide⟩ 2 hp)) T117_29
      hfix117_29 hinj117_29 hcardT117_29
      (fun i => conj_mem_of_fixedPoints _ _ (T117_29 i) (hfix117_29 i) _)
      ⟨117, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 2 hp) Q2.T117_29_2 Q2.hfix117_29_2 Q2.hinj117_29_2
      Q2.hcardT117_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_29_2 i) (Q2.hfix117_29_2 i) _)
      colCert_117_29_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_29_3 (hp : 3 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 3 (transLenTr ⟨29, by decide⟩ 3 hp)) T117_29
      hfix117_29 hinj117_29 hcardT117_29
      (fun i => conj_mem_of_fixedPoints _ _ (T117_29 i) (hfix117_29 i) _)
      ⟨117, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 3 hp) Q2.T117_29_2 Q2.hfix117_29_2 Q2.hinj117_29_2
      Q2.hcardT117_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_29_2 i) (Q2.hfix117_29_2 i) _)
      colCert_117_29_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_29_4 (hp : 4 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 4 (transLenTr ⟨29, by decide⟩ 4 hp)) T117_29
      hfix117_29 hinj117_29 hcardT117_29
      (fun i => conj_mem_of_fixedPoints _ _ (T117_29 i) (hfix117_29 i) _)
      ⟨117, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 4 hp) Q2.T117_29_2 Q2.hfix117_29_2 Q2.hinj117_29_2
      Q2.hcardT117_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_29_2 i) (Q2.hfix117_29_2 i) _)
      colCert_117_29_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_29_5 (hp : 5 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 5 (transLenTr ⟨29, by decide⟩ 5 hp)) T117_29
      hfix117_29 hinj117_29 hcardT117_29
      (fun i => conj_mem_of_fixedPoints _ _ (T117_29 i) (hfix117_29 i) _)
      ⟨117, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 5 hp) Q2.T117_29_2 Q2.hfix117_29_2 Q2.hinj117_29_2
      Q2.hcardT117_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_29_2 i) (Q2.hfix117_29_2 i) _)
      colCert_117_29_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_29_10 (hp : 10 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 10 (transLenTr ⟨29, by decide⟩ 10 hp)) T117_29
      hfix117_29 hinj117_29 hcardT117_29
      (fun i => conj_mem_of_fixedPoints _ _ (T117_29 i) (hfix117_29 i) _)
      ⟨117, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 10 hp) Q2.T117_29_2 Q2.hfix117_29_2 Q2.hinj117_29_2
      Q2.hcardT117_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_29_2 i) (Q2.hfix117_29_2 i) _)
      colCert_117_29_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_29_15 (hp : 15 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 15 (transLenTr ⟨29, by decide⟩ 15 hp)) T117_29
      hfix117_29 hinj117_29 hcardT117_29
      (fun i => conj_mem_of_fixedPoints _ _ (T117_29 i) (hfix117_29 i) _)
      ⟨117, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 15 hp) Q2.T117_29_2 Q2.hfix117_29_2 Q2.hinj117_29_2
      Q2.hcardT117_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_29_2 i) (Q2.hfix117_29_2 i) _)
      colCert_117_29_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_29_20 (hp : 20 < (Q2.transData.getD 29 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨29, by decide⟩ : Fin 148)) (colE2 ⟨29, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨29, by decide⟩ : Fin 148))
        (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨29, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨29, by decide⟩ 20 (transLenTr ⟨29, by decide⟩ 20 hp)) T117_29
      hfix117_29 hinj117_29 hcardT117_29
      (fun i => conj_mem_of_fixedPoints _ _ (T117_29 i) (hfix117_29 i) _)
      ⟨117, by decide⟩ ⟨29, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨29, by decide⟩ 20 hp) Q2.T117_29_2 Q2.hfix117_29_2 Q2.hinj117_29_2
      Q2.hcardT117_29_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_29_2 i) (Q2.hfix117_29_2 i) _)
      colCert_117_29_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_34_0 (hp : 0 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 0 (transLenTr ⟨34, by decide⟩ 0 hp)) T117_34
      hfix117_34 hinj117_34 hcardT117_34
      (fun i => conj_mem_of_fixedPoints _ _ (T117_34 i) (hfix117_34 i) _)
      ⟨117, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 0 hp) Q2.T117_34_2 Q2.hfix117_34_2 Q2.hinj117_34_2
      Q2.hcardT117_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_34_2 i) (Q2.hfix117_34_2 i) _)
      colCert_117_34_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_34_1 (hp : 1 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 1 (transLenTr ⟨34, by decide⟩ 1 hp)) T117_34
      hfix117_34 hinj117_34 hcardT117_34
      (fun i => conj_mem_of_fixedPoints _ _ (T117_34 i) (hfix117_34 i) _)
      ⟨117, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 1 hp) Q2.T117_34_2 Q2.hfix117_34_2 Q2.hinj117_34_2
      Q2.hcardT117_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_34_2 i) (Q2.hfix117_34_2 i) _)
      colCert_117_34_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_34_2 (hp : 2 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 2 (transLenTr ⟨34, by decide⟩ 2 hp)) T117_34
      hfix117_34 hinj117_34 hcardT117_34
      (fun i => conj_mem_of_fixedPoints _ _ (T117_34 i) (hfix117_34 i) _)
      ⟨117, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 2 hp) Q2.T117_34_2 Q2.hfix117_34_2 Q2.hinj117_34_2
      Q2.hcardT117_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_34_2 i) (Q2.hfix117_34_2 i) _)
      colCert_117_34_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_34_3 (hp : 3 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 3 (transLenTr ⟨34, by decide⟩ 3 hp)) T117_34
      hfix117_34 hinj117_34 hcardT117_34
      (fun i => conj_mem_of_fixedPoints _ _ (T117_34 i) (hfix117_34 i) _)
      ⟨117, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 3 hp) Q2.T117_34_2 Q2.hfix117_34_2 Q2.hinj117_34_2
      Q2.hcardT117_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_34_2 i) (Q2.hfix117_34_2 i) _)
      colCert_117_34_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_34_4 (hp : 4 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 4 (transLenTr ⟨34, by decide⟩ 4 hp)) T117_34
      hfix117_34 hinj117_34 hcardT117_34
      (fun i => conj_mem_of_fixedPoints _ _ (T117_34 i) (hfix117_34 i) _)
      ⟨117, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 4 hp) Q2.T117_34_2 Q2.hfix117_34_2 Q2.hinj117_34_2
      Q2.hcardT117_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_34_2 i) (Q2.hfix117_34_2 i) _)
      colCert_117_34_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_34_5 (hp : 5 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 5 (transLenTr ⟨34, by decide⟩ 5 hp)) T117_34
      hfix117_34 hinj117_34 hcardT117_34
      (fun i => conj_mem_of_fixedPoints _ _ (T117_34 i) (hfix117_34 i) _)
      ⟨117, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 5 hp) Q2.T117_34_2 Q2.hfix117_34_2 Q2.hinj117_34_2
      Q2.hcardT117_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_34_2 i) (Q2.hfix117_34_2 i) _)
      colCert_117_34_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_34_10 (hp : 10 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 10 (transLenTr ⟨34, by decide⟩ 10 hp)) T117_34
      hfix117_34 hinj117_34 hcardT117_34
      (fun i => conj_mem_of_fixedPoints _ _ (T117_34 i) (hfix117_34 i) _)
      ⟨117, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 10 hp) Q2.T117_34_2 Q2.hfix117_34_2 Q2.hinj117_34_2
      Q2.hcardT117_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_34_2 i) (Q2.hfix117_34_2 i) _)
      colCert_117_34_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_34_15 (hp : 15 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 15 (transLenTr ⟨34, by decide⟩ 15 hp)) T117_34
      hfix117_34 hinj117_34 hcardT117_34
      (fun i => conj_mem_of_fixedPoints _ _ (T117_34 i) (hfix117_34 i) _)
      ⟨117, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 15 hp) Q2.T117_34_2 Q2.hfix117_34_2 Q2.hinj117_34_2
      Q2.hcardT117_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_34_2 i) (Q2.hfix117_34_2 i) _)
      colCert_117_34_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_34_20 (hp : 20 < (Q2.transData.getD 34 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨34, by decide⟩ : Fin 148)) (colE2 ⟨34, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨34, by decide⟩ : Fin 148))
        (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨34, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨34, by decide⟩ 20 (transLenTr ⟨34, by decide⟩ 20 hp)) T117_34
      hfix117_34 hinj117_34 hcardT117_34
      (fun i => conj_mem_of_fixedPoints _ _ (T117_34 i) (hfix117_34 i) _)
      ⟨117, by decide⟩ ⟨34, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨34, by decide⟩ 20 hp) Q2.T117_34_2 Q2.hfix117_34_2 Q2.hinj117_34_2
      Q2.hcardT117_34_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_34_2 i) (Q2.hfix117_34_2 i) _)
      colCert_117_34_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_39_0 (hp : 0 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 0 (transLenTr ⟨39, by decide⟩ 0 hp)) T117_39
      hfix117_39 hinj117_39 hcardT117_39
      (fun i => conj_mem_of_fixedPoints _ _ (T117_39 i) (hfix117_39 i) _)
      ⟨117, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 0 hp) Q2.T117_39_2 Q2.hfix117_39_2 Q2.hinj117_39_2
      Q2.hcardT117_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_39_2 i) (Q2.hfix117_39_2 i) _)
      colCert_117_39_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_39_1 (hp : 1 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 1 (transLenTr ⟨39, by decide⟩ 1 hp)) T117_39
      hfix117_39 hinj117_39 hcardT117_39
      (fun i => conj_mem_of_fixedPoints _ _ (T117_39 i) (hfix117_39 i) _)
      ⟨117, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 1 hp) Q2.T117_39_2 Q2.hfix117_39_2 Q2.hinj117_39_2
      Q2.hcardT117_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_39_2 i) (Q2.hfix117_39_2 i) _)
      colCert_117_39_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_39_2 (hp : 2 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 2 (transLenTr ⟨39, by decide⟩ 2 hp)) T117_39
      hfix117_39 hinj117_39 hcardT117_39
      (fun i => conj_mem_of_fixedPoints _ _ (T117_39 i) (hfix117_39 i) _)
      ⟨117, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 2 hp) Q2.T117_39_2 Q2.hfix117_39_2 Q2.hinj117_39_2
      Q2.hcardT117_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_39_2 i) (Q2.hfix117_39_2 i) _)
      colCert_117_39_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_39_3 (hp : 3 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 3 (transLenTr ⟨39, by decide⟩ 3 hp)) T117_39
      hfix117_39 hinj117_39 hcardT117_39
      (fun i => conj_mem_of_fixedPoints _ _ (T117_39 i) (hfix117_39 i) _)
      ⟨117, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 3 hp) Q2.T117_39_2 Q2.hfix117_39_2 Q2.hinj117_39_2
      Q2.hcardT117_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_39_2 i) (Q2.hfix117_39_2 i) _)
      colCert_117_39_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_39_4 (hp : 4 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 4 (transLenTr ⟨39, by decide⟩ 4 hp)) T117_39
      hfix117_39 hinj117_39 hcardT117_39
      (fun i => conj_mem_of_fixedPoints _ _ (T117_39 i) (hfix117_39 i) _)
      ⟨117, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 4 hp) Q2.T117_39_2 Q2.hfix117_39_2 Q2.hinj117_39_2
      Q2.hcardT117_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_39_2 i) (Q2.hfix117_39_2 i) _)
      colCert_117_39_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_39_5 (hp : 5 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 5 (transLenTr ⟨39, by decide⟩ 5 hp)) T117_39
      hfix117_39 hinj117_39 hcardT117_39
      (fun i => conj_mem_of_fixedPoints _ _ (T117_39 i) (hfix117_39 i) _)
      ⟨117, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 5 hp) Q2.T117_39_2 Q2.hfix117_39_2 Q2.hinj117_39_2
      Q2.hcardT117_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_39_2 i) (Q2.hfix117_39_2 i) _)
      colCert_117_39_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_39_10 (hp : 10 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 10 (transLenTr ⟨39, by decide⟩ 10 hp)) T117_39
      hfix117_39 hinj117_39 hcardT117_39
      (fun i => conj_mem_of_fixedPoints _ _ (T117_39 i) (hfix117_39 i) _)
      ⟨117, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 10 hp) Q2.T117_39_2 Q2.hfix117_39_2 Q2.hinj117_39_2
      Q2.hcardT117_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_39_2 i) (Q2.hfix117_39_2 i) _)
      colCert_117_39_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_39_15 (hp : 15 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 15 (transLenTr ⟨39, by decide⟩ 15 hp)) T117_39
      hfix117_39 hinj117_39 hcardT117_39
      (fun i => conj_mem_of_fixedPoints _ _ (T117_39 i) (hfix117_39 i) _)
      ⟨117, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 15 hp) Q2.T117_39_2 Q2.hfix117_39_2 Q2.hinj117_39_2
      Q2.hcardT117_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_39_2 i) (Q2.hfix117_39_2 i) _)
      colCert_117_39_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_39_20 (hp : 20 < (Q2.transData.getD 39 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨39, by decide⟩ : Fin 148)) (colE2 ⟨39, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨39, by decide⟩ : Fin 148))
        (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨39, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨39, by decide⟩ 20 (transLenTr ⟨39, by decide⟩ 20 hp)) T117_39
      hfix117_39 hinj117_39 hcardT117_39
      (fun i => conj_mem_of_fixedPoints _ _ (T117_39 i) (hfix117_39 i) _)
      ⟨117, by decide⟩ ⟨39, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨39, by decide⟩ 20 hp) Q2.T117_39_2 Q2.hfix117_39_2 Q2.hinj117_39_2
      Q2.hcardT117_39_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_39_2 i) (Q2.hfix117_39_2 i) _)
      colCert_117_39_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_44_0 (hp : 0 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 0 (transLenTr ⟨44, by decide⟩ 0 hp)) T117_44
      hfix117_44 hinj117_44 hcardT117_44
      (fun i => conj_mem_of_fixedPoints _ _ (T117_44 i) (hfix117_44 i) _)
      ⟨117, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 0 hp) Q2.T117_44_2 Q2.hfix117_44_2 Q2.hinj117_44_2
      Q2.hcardT117_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_44_2 i) (Q2.hfix117_44_2 i) _)
      colCert_117_44_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_44_1 (hp : 1 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 1 (transLenTr ⟨44, by decide⟩ 1 hp)) T117_44
      hfix117_44 hinj117_44 hcardT117_44
      (fun i => conj_mem_of_fixedPoints _ _ (T117_44 i) (hfix117_44 i) _)
      ⟨117, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 1 hp) Q2.T117_44_2 Q2.hfix117_44_2 Q2.hinj117_44_2
      Q2.hcardT117_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_44_2 i) (Q2.hfix117_44_2 i) _)
      colCert_117_44_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_44_2 (hp : 2 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 2 (transLenTr ⟨44, by decide⟩ 2 hp)) T117_44
      hfix117_44 hinj117_44 hcardT117_44
      (fun i => conj_mem_of_fixedPoints _ _ (T117_44 i) (hfix117_44 i) _)
      ⟨117, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 2 hp) Q2.T117_44_2 Q2.hfix117_44_2 Q2.hinj117_44_2
      Q2.hcardT117_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_44_2 i) (Q2.hfix117_44_2 i) _)
      colCert_117_44_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_44_3 (hp : 3 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 3 (transLenTr ⟨44, by decide⟩ 3 hp)) T117_44
      hfix117_44 hinj117_44 hcardT117_44
      (fun i => conj_mem_of_fixedPoints _ _ (T117_44 i) (hfix117_44 i) _)
      ⟨117, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 3 hp) Q2.T117_44_2 Q2.hfix117_44_2 Q2.hinj117_44_2
      Q2.hcardT117_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_44_2 i) (Q2.hfix117_44_2 i) _)
      colCert_117_44_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_44_4 (hp : 4 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 4 (transLenTr ⟨44, by decide⟩ 4 hp)) T117_44
      hfix117_44 hinj117_44 hcardT117_44
      (fun i => conj_mem_of_fixedPoints _ _ (T117_44 i) (hfix117_44 i) _)
      ⟨117, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 4 hp) Q2.T117_44_2 Q2.hfix117_44_2 Q2.hinj117_44_2
      Q2.hcardT117_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_44_2 i) (Q2.hfix117_44_2 i) _)
      colCert_117_44_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_44_5 (hp : 5 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 5 (transLenTr ⟨44, by decide⟩ 5 hp)) T117_44
      hfix117_44 hinj117_44 hcardT117_44
      (fun i => conj_mem_of_fixedPoints _ _ (T117_44 i) (hfix117_44 i) _)
      ⟨117, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 5 hp) Q2.T117_44_2 Q2.hfix117_44_2 Q2.hinj117_44_2
      Q2.hcardT117_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_44_2 i) (Q2.hfix117_44_2 i) _)
      colCert_117_44_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_44_10 (hp : 10 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 10 (transLenTr ⟨44, by decide⟩ 10 hp)) T117_44
      hfix117_44 hinj117_44 hcardT117_44
      (fun i => conj_mem_of_fixedPoints _ _ (T117_44 i) (hfix117_44 i) _)
      ⟨117, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 10 hp) Q2.T117_44_2 Q2.hfix117_44_2 Q2.hinj117_44_2
      Q2.hcardT117_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_44_2 i) (Q2.hfix117_44_2 i) _)
      colCert_117_44_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_44_15 (hp : 15 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 15 (transLenTr ⟨44, by decide⟩ 15 hp)) T117_44
      hfix117_44 hinj117_44 hcardT117_44
      (fun i => conj_mem_of_fixedPoints _ _ (T117_44 i) (hfix117_44 i) _)
      ⟨117, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 15 hp) Q2.T117_44_2 Q2.hfix117_44_2 Q2.hinj117_44_2
      Q2.hcardT117_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_44_2 i) (Q2.hfix117_44_2 i) _)
      colCert_117_44_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_44_20 (hp : 20 < (Q2.transData.getD 44 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨44, by decide⟩ : Fin 148)) (colE2 ⟨44, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨44, by decide⟩ : Fin 148))
        (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨44, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨44, by decide⟩ 20 (transLenTr ⟨44, by decide⟩ 20 hp)) T117_44
      hfix117_44 hinj117_44 hcardT117_44
      (fun i => conj_mem_of_fixedPoints _ _ (T117_44 i) (hfix117_44 i) _)
      ⟨117, by decide⟩ ⟨44, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨44, by decide⟩ 20 hp) Q2.T117_44_2 Q2.hfix117_44_2 Q2.hinj117_44_2
      Q2.hcardT117_44_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_44_2 i) (Q2.hfix117_44_2 i) _)
      colCert_117_44_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_49_0 (hp : 0 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 0 (transLenTr ⟨49, by decide⟩ 0 hp)) T117_49
      hfix117_49 hinj117_49 hcardT117_49
      (fun i => conj_mem_of_fixedPoints _ _ (T117_49 i) (hfix117_49 i) _)
      ⟨117, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 0 hp) Q2.T117_49_2 Q2.hfix117_49_2 Q2.hinj117_49_2
      Q2.hcardT117_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_49_2 i) (Q2.hfix117_49_2 i) _)
      colCert_117_49_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_49_1 (hp : 1 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 1 (transLenTr ⟨49, by decide⟩ 1 hp)) T117_49
      hfix117_49 hinj117_49 hcardT117_49
      (fun i => conj_mem_of_fixedPoints _ _ (T117_49 i) (hfix117_49 i) _)
      ⟨117, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 1 hp) Q2.T117_49_2 Q2.hfix117_49_2 Q2.hinj117_49_2
      Q2.hcardT117_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_49_2 i) (Q2.hfix117_49_2 i) _)
      colCert_117_49_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_49_2 (hp : 2 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 2 (transLenTr ⟨49, by decide⟩ 2 hp)) T117_49
      hfix117_49 hinj117_49 hcardT117_49
      (fun i => conj_mem_of_fixedPoints _ _ (T117_49 i) (hfix117_49 i) _)
      ⟨117, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 2 hp) Q2.T117_49_2 Q2.hfix117_49_2 Q2.hinj117_49_2
      Q2.hcardT117_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_49_2 i) (Q2.hfix117_49_2 i) _)
      colCert_117_49_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_49_3 (hp : 3 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 3 (transLenTr ⟨49, by decide⟩ 3 hp)) T117_49
      hfix117_49 hinj117_49 hcardT117_49
      (fun i => conj_mem_of_fixedPoints _ _ (T117_49 i) (hfix117_49 i) _)
      ⟨117, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 3 hp) Q2.T117_49_2 Q2.hfix117_49_2 Q2.hinj117_49_2
      Q2.hcardT117_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_49_2 i) (Q2.hfix117_49_2 i) _)
      colCert_117_49_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_49_4 (hp : 4 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 4 (transLenTr ⟨49, by decide⟩ 4 hp)) T117_49
      hfix117_49 hinj117_49 hcardT117_49
      (fun i => conj_mem_of_fixedPoints _ _ (T117_49 i) (hfix117_49 i) _)
      ⟨117, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 4 hp) Q2.T117_49_2 Q2.hfix117_49_2 Q2.hinj117_49_2
      Q2.hcardT117_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_49_2 i) (Q2.hfix117_49_2 i) _)
      colCert_117_49_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_49_5 (hp : 5 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 5 (transLenTr ⟨49, by decide⟩ 5 hp)) T117_49
      hfix117_49 hinj117_49 hcardT117_49
      (fun i => conj_mem_of_fixedPoints _ _ (T117_49 i) (hfix117_49 i) _)
      ⟨117, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 5 hp) Q2.T117_49_2 Q2.hfix117_49_2 Q2.hinj117_49_2
      Q2.hcardT117_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_49_2 i) (Q2.hfix117_49_2 i) _)
      colCert_117_49_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_49_10 (hp : 10 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 10 (transLenTr ⟨49, by decide⟩ 10 hp)) T117_49
      hfix117_49 hinj117_49 hcardT117_49
      (fun i => conj_mem_of_fixedPoints _ _ (T117_49 i) (hfix117_49 i) _)
      ⟨117, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 10 hp) Q2.T117_49_2 Q2.hfix117_49_2 Q2.hinj117_49_2
      Q2.hcardT117_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_49_2 i) (Q2.hfix117_49_2 i) _)
      colCert_117_49_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_49_15 (hp : 15 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 15 (transLenTr ⟨49, by decide⟩ 15 hp)) T117_49
      hfix117_49 hinj117_49 hcardT117_49
      (fun i => conj_mem_of_fixedPoints _ _ (T117_49 i) (hfix117_49 i) _)
      ⟨117, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 15 hp) Q2.T117_49_2 Q2.hfix117_49_2 Q2.hinj117_49_2
      Q2.hcardT117_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_49_2 i) (Q2.hfix117_49_2 i) _)
      colCert_117_49_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_49_20 (hp : 20 < (Q2.transData.getD 49 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨49, by decide⟩ : Fin 148)) (colE2 ⟨49, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨49, by decide⟩ : Fin 148))
        (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨49, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨49, by decide⟩ 20 (transLenTr ⟨49, by decide⟩ 20 hp)) T117_49
      hfix117_49 hinj117_49 hcardT117_49
      (fun i => conj_mem_of_fixedPoints _ _ (T117_49 i) (hfix117_49 i) _)
      ⟨117, by decide⟩ ⟨49, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨49, by decide⟩ 20 hp) Q2.T117_49_2 Q2.hfix117_49_2 Q2.hinj117_49_2
      Q2.hcardT117_49_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_49_2 i) (Q2.hfix117_49_2 i) _)
      colCert_117_49_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_53_0 (hp : 0 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 0 (transLenTr ⟨53, by decide⟩ 0 hp)) T117_53
      hfix117_53 hinj117_53 hcardT117_53
      (fun i => conj_mem_of_fixedPoints _ _ (T117_53 i) (hfix117_53 i) _)
      ⟨117, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 0 hp) Q2.T117_53_2 Q2.hfix117_53_2 Q2.hinj117_53_2
      Q2.hcardT117_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_53_2 i) (Q2.hfix117_53_2 i) _)
      colCert_117_53_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_53_1 (hp : 1 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 1 (transLenTr ⟨53, by decide⟩ 1 hp)) T117_53
      hfix117_53 hinj117_53 hcardT117_53
      (fun i => conj_mem_of_fixedPoints _ _ (T117_53 i) (hfix117_53 i) _)
      ⟨117, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 1 hp) Q2.T117_53_2 Q2.hfix117_53_2 Q2.hinj117_53_2
      Q2.hcardT117_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_53_2 i) (Q2.hfix117_53_2 i) _)
      colCert_117_53_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_53_2 (hp : 2 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 2 (transLenTr ⟨53, by decide⟩ 2 hp)) T117_53
      hfix117_53 hinj117_53 hcardT117_53
      (fun i => conj_mem_of_fixedPoints _ _ (T117_53 i) (hfix117_53 i) _)
      ⟨117, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 2 hp) Q2.T117_53_2 Q2.hfix117_53_2 Q2.hinj117_53_2
      Q2.hcardT117_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_53_2 i) (Q2.hfix117_53_2 i) _)
      colCert_117_53_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_53_3 (hp : 3 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 3 (transLenTr ⟨53, by decide⟩ 3 hp)) T117_53
      hfix117_53 hinj117_53 hcardT117_53
      (fun i => conj_mem_of_fixedPoints _ _ (T117_53 i) (hfix117_53 i) _)
      ⟨117, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 3 hp) Q2.T117_53_2 Q2.hfix117_53_2 Q2.hinj117_53_2
      Q2.hcardT117_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_53_2 i) (Q2.hfix117_53_2 i) _)
      colCert_117_53_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_53_4 (hp : 4 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 4 (transLenTr ⟨53, by decide⟩ 4 hp)) T117_53
      hfix117_53 hinj117_53 hcardT117_53
      (fun i => conj_mem_of_fixedPoints _ _ (T117_53 i) (hfix117_53 i) _)
      ⟨117, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 4 hp) Q2.T117_53_2 Q2.hfix117_53_2 Q2.hinj117_53_2
      Q2.hcardT117_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_53_2 i) (Q2.hfix117_53_2 i) _)
      colCert_117_53_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_53_5 (hp : 5 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 5 (transLenTr ⟨53, by decide⟩ 5 hp)) T117_53
      hfix117_53 hinj117_53 hcardT117_53
      (fun i => conj_mem_of_fixedPoints _ _ (T117_53 i) (hfix117_53 i) _)
      ⟨117, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 5 hp) Q2.T117_53_2 Q2.hfix117_53_2 Q2.hinj117_53_2
      Q2.hcardT117_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_53_2 i) (Q2.hfix117_53_2 i) _)
      colCert_117_53_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_53_10 (hp : 10 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 10 (transLenTr ⟨53, by decide⟩ 10 hp)) T117_53
      hfix117_53 hinj117_53 hcardT117_53
      (fun i => conj_mem_of_fixedPoints _ _ (T117_53 i) (hfix117_53 i) _)
      ⟨117, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 10 hp) Q2.T117_53_2 Q2.hfix117_53_2 Q2.hinj117_53_2
      Q2.hcardT117_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_53_2 i) (Q2.hfix117_53_2 i) _)
      colCert_117_53_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_53_15 (hp : 15 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 15 (transLenTr ⟨53, by decide⟩ 15 hp)) T117_53
      hfix117_53 hinj117_53 hcardT117_53
      (fun i => conj_mem_of_fixedPoints _ _ (T117_53 i) (hfix117_53 i) _)
      ⟨117, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 15 hp) Q2.T117_53_2 Q2.hfix117_53_2 Q2.hinj117_53_2
      Q2.hcardT117_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_53_2 i) (Q2.hfix117_53_2 i) _)
      colCert_117_53_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_53_20 (hp : 20 < (Q2.transData.getD 53 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨53, by decide⟩ : Fin 148)) (colE2 ⟨53, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨53, by decide⟩ : Fin 148))
        (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨53, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨53, by decide⟩ 20 (transLenTr ⟨53, by decide⟩ 20 hp)) T117_53
      hfix117_53 hinj117_53 hcardT117_53
      (fun i => conj_mem_of_fixedPoints _ _ (T117_53 i) (hfix117_53 i) _)
      ⟨117, by decide⟩ ⟨53, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨53, by decide⟩ 20 hp) Q2.T117_53_2 Q2.hfix117_53_2 Q2.hinj117_53_2
      Q2.hcardT117_53_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_53_2 i) (Q2.hfix117_53_2 i) _)
      colCert_117_53_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_0 (hp : 0 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 0 (transLenTr ⟨60, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 0 (transLenTr ⟨60, by decide⟩ 0 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 0 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_1 (hp : 1 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 1 (transLenTr ⟨60, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 1 (transLenTr ⟨60, by decide⟩ 1 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 1 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_2 (hp : 2 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 2 (transLenTr ⟨60, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 2 (transLenTr ⟨60, by decide⟩ 2 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 2 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_3 (hp : 3 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 3 (transLenTr ⟨60, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 3 (transLenTr ⟨60, by decide⟩ 3 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 3 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_4 (hp : 4 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 4 (transLenTr ⟨60, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 4 (transLenTr ⟨60, by decide⟩ 4 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 4 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_5 (hp : 5 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 5 (transLenTr ⟨60, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 5 (transLenTr ⟨60, by decide⟩ 5 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 5 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_6 (hp : 6 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 6 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 6 (transLenTr ⟨60, by decide⟩ 6 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 6 (transLenTr ⟨60, by decide⟩ 6 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 6 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_6.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_7 (hp : 7 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 7 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 7 (transLenTr ⟨60, by decide⟩ 7 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 7 (transLenTr ⟨60, by decide⟩ 7 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 7 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_7.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_8 (hp : 8 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 8 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 8 (transLenTr ⟨60, by decide⟩ 8 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 8 (transLenTr ⟨60, by decide⟩ 8 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 8 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_8.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_9 (hp : 9 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 9 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 9 (transLenTr ⟨60, by decide⟩ 9 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 9 (transLenTr ⟨60, by decide⟩ 9 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 9 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_9.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_10 (hp : 10 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 10 (transLenTr ⟨60, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 10 (transLenTr ⟨60, by decide⟩ 10 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 10 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_11 (hp : 11 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 11 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 11 (transLenTr ⟨60, by decide⟩ 11 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 11 (transLenTr ⟨60, by decide⟩ 11 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 11 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_11.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_12 (hp : 12 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 12 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 12 (transLenTr ⟨60, by decide⟩ 12 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 12 (transLenTr ⟨60, by decide⟩ 12 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 12 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_12.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_13 (hp : 13 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 13 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 13 (transLenTr ⟨60, by decide⟩ 13 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 13 (transLenTr ⟨60, by decide⟩ 13 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 13 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_13.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_14 (hp : 14 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 14 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 14 (transLenTr ⟨60, by decide⟩ 14 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 14 (transLenTr ⟨60, by decide⟩ 14 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 14 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_14.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_15 (hp : 15 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 15 (transLenTr ⟨60, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 15 (transLenTr ⟨60, by decide⟩ 15 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 15 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_16 (hp : 16 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 16 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 16 (transLenTr ⟨60, by decide⟩ 16 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 16 (transLenTr ⟨60, by decide⟩ 16 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 16 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_16.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_17 (hp : 17 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 17 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 17 (transLenTr ⟨60, by decide⟩ 17 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 17 (transLenTr ⟨60, by decide⟩ 17 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 17 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_17.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_18 (hp : 18 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 18 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 18 (transLenTr ⟨60, by decide⟩ 18 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 18 (transLenTr ⟨60, by decide⟩ 18 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 18 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_18.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_19 (hp : 19 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 19 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 19 (transLenTr ⟨60, by decide⟩ 19 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 19 (transLenTr ⟨60, by decide⟩ 19 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 19 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_19.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_20 (hp : 20 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 20 (transLenTr ⟨60, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 20 (transLenTr ⟨60, by decide⟩ 20 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 20 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_21 (hp : 21 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 21 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 21 (transLenTr ⟨60, by decide⟩ 21 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 21 (transLenTr ⟨60, by decide⟩ 21 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 21 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_21.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_22 (hp : 22 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 22 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 22 (transLenTr ⟨60, by decide⟩ 22 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 22 (transLenTr ⟨60, by decide⟩ 22 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 22 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_22.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_23 (hp : 23 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 23 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 23 (transLenTr ⟨60, by decide⟩ 23 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 23 (transLenTr ⟨60, by decide⟩ 23 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 23 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_23.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_60_24 (hp : 24 < (Q2.transData.getD 60 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨60, by decide⟩ : Fin 148)) (colE2 ⟨60, by decide⟩ 24 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨60, by decide⟩ : Fin 148))
        (colE1 ⟨60, by decide⟩ 24 (transLenTr ⟨60, by decide⟩ 24 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨60, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨60, by decide⟩ 24 (transLenTr ⟨60, by decide⟩ 24 hp)) T117_60
      hfix117_60 hinj117_60 hcardT117_60
      (fun i => conj_mem_of_fixedPoints _ _ (T117_60 i) (hfix117_60 i) _)
      ⟨117, by decide⟩ ⟨60, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨60, by decide⟩ 24 hp) Q2.T117_60_2 Q2.hfix117_60_2 Q2.hinj117_60_2
      Q2.hcardT117_60_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_60_2 i) (Q2.hfix117_60_2 i) _)
      colCert_117_60_24.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_0 (hp : 0 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 0 (transLenTr ⟨61, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 0 (transLenTr ⟨61, by decide⟩ 0 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 0 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_1 (hp : 1 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 1 (transLenTr ⟨61, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 1 (transLenTr ⟨61, by decide⟩ 1 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 1 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_2 (hp : 2 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 2 (transLenTr ⟨61, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 2 (transLenTr ⟨61, by decide⟩ 2 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 2 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_3 (hp : 3 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 3 (transLenTr ⟨61, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 3 (transLenTr ⟨61, by decide⟩ 3 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 3 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_4 (hp : 4 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 4 (transLenTr ⟨61, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 4 (transLenTr ⟨61, by decide⟩ 4 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 4 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_5 (hp : 5 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 5 (transLenTr ⟨61, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 5 (transLenTr ⟨61, by decide⟩ 5 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 5 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_6 (hp : 6 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 6 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 6 (transLenTr ⟨61, by decide⟩ 6 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 6 (transLenTr ⟨61, by decide⟩ 6 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 6 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_6.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_7 (hp : 7 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 7 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 7 (transLenTr ⟨61, by decide⟩ 7 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 7 (transLenTr ⟨61, by decide⟩ 7 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 7 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_7.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_8 (hp : 8 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 8 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 8 (transLenTr ⟨61, by decide⟩ 8 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 8 (transLenTr ⟨61, by decide⟩ 8 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 8 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_8.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_9 (hp : 9 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 9 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 9 (transLenTr ⟨61, by decide⟩ 9 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 9 (transLenTr ⟨61, by decide⟩ 9 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 9 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_9.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_10 (hp : 10 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 10 (transLenTr ⟨61, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 10 (transLenTr ⟨61, by decide⟩ 10 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 10 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_11 (hp : 11 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 11 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 11 (transLenTr ⟨61, by decide⟩ 11 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 11 (transLenTr ⟨61, by decide⟩ 11 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 11 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_11.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_12 (hp : 12 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 12 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 12 (transLenTr ⟨61, by decide⟩ 12 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 12 (transLenTr ⟨61, by decide⟩ 12 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 12 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_12.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_13 (hp : 13 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 13 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 13 (transLenTr ⟨61, by decide⟩ 13 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 13 (transLenTr ⟨61, by decide⟩ 13 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 13 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_13.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_14 (hp : 14 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 14 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 14 (transLenTr ⟨61, by decide⟩ 14 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 14 (transLenTr ⟨61, by decide⟩ 14 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 14 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_14.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_15 (hp : 15 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 15 (transLenTr ⟨61, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 15 (transLenTr ⟨61, by decide⟩ 15 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 15 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_16 (hp : 16 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 16 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 16 (transLenTr ⟨61, by decide⟩ 16 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 16 (transLenTr ⟨61, by decide⟩ 16 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 16 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_16.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_17 (hp : 17 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 17 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 17 (transLenTr ⟨61, by decide⟩ 17 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 17 (transLenTr ⟨61, by decide⟩ 17 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 17 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_17.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_18 (hp : 18 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 18 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 18 (transLenTr ⟨61, by decide⟩ 18 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 18 (transLenTr ⟨61, by decide⟩ 18 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 18 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_18.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_19 (hp : 19 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 19 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 19 (transLenTr ⟨61, by decide⟩ 19 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 19 (transLenTr ⟨61, by decide⟩ 19 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 19 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_19.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_20 (hp : 20 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 20 (transLenTr ⟨61, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 20 (transLenTr ⟨61, by decide⟩ 20 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 20 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_21 (hp : 21 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 21 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 21 (transLenTr ⟨61, by decide⟩ 21 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 21 (transLenTr ⟨61, by decide⟩ 21 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 21 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_21.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_22 (hp : 22 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 22 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 22 (transLenTr ⟨61, by decide⟩ 22 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 22 (transLenTr ⟨61, by decide⟩ 22 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 22 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_22.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_23 (hp : 23 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 23 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 23 (transLenTr ⟨61, by decide⟩ 23 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 23 (transLenTr ⟨61, by decide⟩ 23 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 23 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_23.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_61_24 (hp : 24 < (Q2.transData.getD 61 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨61, by decide⟩ : Fin 148)) (colE2 ⟨61, by decide⟩ 24 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨61, by decide⟩ : Fin 148))
        (colE1 ⟨61, by decide⟩ 24 (transLenTr ⟨61, by decide⟩ 24 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨61, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨61, by decide⟩ 24 (transLenTr ⟨61, by decide⟩ 24 hp)) T117_61
      hfix117_61 hinj117_61 hcardT117_61
      (fun i => conj_mem_of_fixedPoints _ _ (T117_61 i) (hfix117_61 i) _)
      ⟨117, by decide⟩ ⟨61, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨61, by decide⟩ 24 hp) Q2.T117_61_2 Q2.hfix117_61_2 Q2.hinj117_61_2
      Q2.hcardT117_61_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_61_2 i) (Q2.hfix117_61_2 i) _)
      colCert_117_61_24.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_0 (hp : 0 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 0 (transLenTr ⟨62, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 0 (transLenTr ⟨62, by decide⟩ 0 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 0 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_1 (hp : 1 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 1 (transLenTr ⟨62, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 1 (transLenTr ⟨62, by decide⟩ 1 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 1 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_2 (hp : 2 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 2 (transLenTr ⟨62, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 2 (transLenTr ⟨62, by decide⟩ 2 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 2 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_3 (hp : 3 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 3 (transLenTr ⟨62, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 3 (transLenTr ⟨62, by decide⟩ 3 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 3 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_4 (hp : 4 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 4 (transLenTr ⟨62, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 4 (transLenTr ⟨62, by decide⟩ 4 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 4 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_5 (hp : 5 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 5 (transLenTr ⟨62, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 5 (transLenTr ⟨62, by decide⟩ 5 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 5 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_6 (hp : 6 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 6 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 6 (transLenTr ⟨62, by decide⟩ 6 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 6 (transLenTr ⟨62, by decide⟩ 6 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 6 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_6.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_7 (hp : 7 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 7 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 7 (transLenTr ⟨62, by decide⟩ 7 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 7 (transLenTr ⟨62, by decide⟩ 7 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 7 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_7.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_8 (hp : 8 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 8 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 8 (transLenTr ⟨62, by decide⟩ 8 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 8 (transLenTr ⟨62, by decide⟩ 8 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 8 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_8.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_9 (hp : 9 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 9 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 9 (transLenTr ⟨62, by decide⟩ 9 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 9 (transLenTr ⟨62, by decide⟩ 9 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 9 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_9.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_10 (hp : 10 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 10 (transLenTr ⟨62, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 10 (transLenTr ⟨62, by decide⟩ 10 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 10 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_11 (hp : 11 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 11 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 11 (transLenTr ⟨62, by decide⟩ 11 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 11 (transLenTr ⟨62, by decide⟩ 11 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 11 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_11.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_12 (hp : 12 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 12 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 12 (transLenTr ⟨62, by decide⟩ 12 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 12 (transLenTr ⟨62, by decide⟩ 12 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 12 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_12.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_13 (hp : 13 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 13 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 13 (transLenTr ⟨62, by decide⟩ 13 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 13 (transLenTr ⟨62, by decide⟩ 13 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 13 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_13.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_14 (hp : 14 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 14 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 14 (transLenTr ⟨62, by decide⟩ 14 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 14 (transLenTr ⟨62, by decide⟩ 14 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 14 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_14.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_15 (hp : 15 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 15 (transLenTr ⟨62, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 15 (transLenTr ⟨62, by decide⟩ 15 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 15 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_16 (hp : 16 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 16 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 16 (transLenTr ⟨62, by decide⟩ 16 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 16 (transLenTr ⟨62, by decide⟩ 16 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 16 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_16.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_17 (hp : 17 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 17 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 17 (transLenTr ⟨62, by decide⟩ 17 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 17 (transLenTr ⟨62, by decide⟩ 17 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 17 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_17.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_18 (hp : 18 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 18 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 18 (transLenTr ⟨62, by decide⟩ 18 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 18 (transLenTr ⟨62, by decide⟩ 18 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 18 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_18.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_19 (hp : 19 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 19 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 19 (transLenTr ⟨62, by decide⟩ 19 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 19 (transLenTr ⟨62, by decide⟩ 19 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 19 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_19.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_20 (hp : 20 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 20 (transLenTr ⟨62, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 20 (transLenTr ⟨62, by decide⟩ 20 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 20 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_21 (hp : 21 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 21 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 21 (transLenTr ⟨62, by decide⟩ 21 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 21 (transLenTr ⟨62, by decide⟩ 21 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 21 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_21.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_22 (hp : 22 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 22 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 22 (transLenTr ⟨62, by decide⟩ 22 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 22 (transLenTr ⟨62, by decide⟩ 22 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 22 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_22.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_23 (hp : 23 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 23 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 23 (transLenTr ⟨62, by decide⟩ 23 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 23 (transLenTr ⟨62, by decide⟩ 23 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 23 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_23.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_62_24 (hp : 24 < (Q2.transData.getD 62 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨62, by decide⟩ : Fin 148)) (colE2 ⟨62, by decide⟩ 24 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨62, by decide⟩ : Fin 148))
        (colE1 ⟨62, by decide⟩ 24 (transLenTr ⟨62, by decide⟩ 24 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨62, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨62, by decide⟩ 24 (transLenTr ⟨62, by decide⟩ 24 hp)) T117_62
      hfix117_62 hinj117_62 hcardT117_62
      (fun i => conj_mem_of_fixedPoints _ _ (T117_62 i) (hfix117_62 i) _)
      ⟨117, by decide⟩ ⟨62, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨62, by decide⟩ 24 hp) Q2.T117_62_2 Q2.hfix117_62_2 Q2.hinj117_62_2
      Q2.hcardT117_62_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_62_2 i) (Q2.hfix117_62_2 i) _)
      colCert_117_62_24.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_63_0 (hp : 0 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 0 (transLenTr ⟨63, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 0 (transLenTr ⟨63, by decide⟩ 0 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 0 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      colCert_117_63_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_63_1 (hp : 1 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 1 (transLenTr ⟨63, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 1 (transLenTr ⟨63, by decide⟩ 1 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 1 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      colCert_117_63_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_63_2 (hp : 2 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 2 (transLenTr ⟨63, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 2 (transLenTr ⟨63, by decide⟩ 2 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 2 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      colCert_117_63_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_63_3 (hp : 3 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 3 (transLenTr ⟨63, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 3 (transLenTr ⟨63, by decide⟩ 3 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 3 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      colCert_117_63_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_63_4 (hp : 4 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 4 (transLenTr ⟨63, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 4 (transLenTr ⟨63, by decide⟩ 4 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 4 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      colCert_117_63_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_63_5 (hp : 5 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 5 (transLenTr ⟨63, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 5 (transLenTr ⟨63, by decide⟩ 5 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 5 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 5 (transLenTr ⟨63, by decide⟩ 5 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_5.D1 (m := 5) from colCertDiv_117_63_5.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 5 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_5.D2 (m := 5) from colCertDiv_117_63_5.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_5_match


theorem leaf_117_63_6 (hp : 6 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 6 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 6 (transLenTr ⟨63, by decide⟩ 6 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 6 (transLenTr ⟨63, by decide⟩ 6 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 6 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 6 (transLenTr ⟨63, by decide⟩ 6 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_6.D1 (m := 5) from colCertDiv_117_63_6.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 6 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_6.D2 (m := 5) from colCertDiv_117_63_6.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_6_match


theorem leaf_117_63_7 (hp : 7 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 7 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 7 (transLenTr ⟨63, by decide⟩ 7 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 7 (transLenTr ⟨63, by decide⟩ 7 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 7 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 7 (transLenTr ⟨63, by decide⟩ 7 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_7.D1 (m := 5) from colCertDiv_117_63_7.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 7 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_7.D2 (m := 5) from colCertDiv_117_63_7.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_7_match


theorem leaf_117_63_8 (hp : 8 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 8 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 8 (transLenTr ⟨63, by decide⟩ 8 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 8 (transLenTr ⟨63, by decide⟩ 8 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 8 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 8 (transLenTr ⟨63, by decide⟩ 8 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_8.D1 (m := 5) from colCertDiv_117_63_8.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 8 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_8.D2 (m := 5) from colCertDiv_117_63_8.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_8_match


theorem leaf_117_63_9 (hp : 9 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 9 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 9 (transLenTr ⟨63, by decide⟩ 9 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 9 (transLenTr ⟨63, by decide⟩ 9 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 9 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 9 (transLenTr ⟨63, by decide⟩ 9 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_9.D1 (m := 5) from colCertDiv_117_63_9.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 9 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_9.D2 (m := 5) from colCertDiv_117_63_9.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_9_match


theorem leaf_117_63_10 (hp : 10 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 10 (transLenTr ⟨63, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 10 (transLenTr ⟨63, by decide⟩ 10 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 10 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 10 (transLenTr ⟨63, by decide⟩ 10 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_10.D1 (m := 5) from colCertDiv_117_63_10.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 10 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_10.D2 (m := 5) from colCertDiv_117_63_10.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_10_match


theorem leaf_117_63_11 (hp : 11 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 11 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 11 (transLenTr ⟨63, by decide⟩ 11 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 11 (transLenTr ⟨63, by decide⟩ 11 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 11 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 11 (transLenTr ⟨63, by decide⟩ 11 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_11.D1 (m := 5) from colCertDiv_117_63_11.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 11 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_11.D2 (m := 5) from colCertDiv_117_63_11.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_11_match


theorem leaf_117_63_12 (hp : 12 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 12 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 12 (transLenTr ⟨63, by decide⟩ 12 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 12 (transLenTr ⟨63, by decide⟩ 12 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 12 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 12 (transLenTr ⟨63, by decide⟩ 12 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_12.D1 (m := 5) from colCertDiv_117_63_12.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 12 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_12.D2 (m := 5) from colCertDiv_117_63_12.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_12_match


theorem leaf_117_63_13 (hp : 13 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 13 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 13 (transLenTr ⟨63, by decide⟩ 13 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 13 (transLenTr ⟨63, by decide⟩ 13 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 13 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 13 (transLenTr ⟨63, by decide⟩ 13 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_13.D1 (m := 5) from colCertDiv_117_63_13.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 13 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_13.D2 (m := 5) from colCertDiv_117_63_13.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_13_match


theorem leaf_117_63_14 (hp : 14 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 14 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 14 (transLenTr ⟨63, by decide⟩ 14 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 14 (transLenTr ⟨63, by decide⟩ 14 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 14 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 14 (transLenTr ⟨63, by decide⟩ 14 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_14.D1 (m := 5) from colCertDiv_117_63_14.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 14 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_14.D2 (m := 5) from colCertDiv_117_63_14.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_14_match


theorem leaf_117_63_15 (hp : 15 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 15 (transLenTr ⟨63, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 15 (transLenTr ⟨63, by decide⟩ 15 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 15 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 15 (transLenTr ⟨63, by decide⟩ 15 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_15.D1 (m := 5) from colCertDiv_117_63_15.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 15 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_15.D2 (m := 5) from colCertDiv_117_63_15.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_15_match


theorem leaf_117_63_16 (hp : 16 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 16 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 16 (transLenTr ⟨63, by decide⟩ 16 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 16 (transLenTr ⟨63, by decide⟩ 16 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 16 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 16 (transLenTr ⟨63, by decide⟩ 16 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_16.D1 (m := 5) from colCertDiv_117_63_16.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 16 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_16.D2 (m := 5) from colCertDiv_117_63_16.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_16_match


theorem leaf_117_63_17 (hp : 17 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 17 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 17 (transLenTr ⟨63, by decide⟩ 17 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 17 (transLenTr ⟨63, by decide⟩ 17 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 17 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 17 (transLenTr ⟨63, by decide⟩ 17 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_17.D1 (m := 5) from colCertDiv_117_63_17.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 17 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_17.D2 (m := 5) from colCertDiv_117_63_17.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_17_match


theorem leaf_117_63_18 (hp : 18 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 18 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 18 (transLenTr ⟨63, by decide⟩ 18 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 18 (transLenTr ⟨63, by decide⟩ 18 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 18 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 18 (transLenTr ⟨63, by decide⟩ 18 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_18.D1 (m := 5) from colCertDiv_117_63_18.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 18 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_18.D2 (m := 5) from colCertDiv_117_63_18.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_18_match


theorem leaf_117_63_19 (hp : 19 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 19 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 19 (transLenTr ⟨63, by decide⟩ 19 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 19 (transLenTr ⟨63, by decide⟩ 19 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 19 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 19 (transLenTr ⟨63, by decide⟩ 19 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_19.D1 (m := 5) from colCertDiv_117_63_19.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 19 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_19.D2 (m := 5) from colCertDiv_117_63_19.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_19_match


theorem leaf_117_63_20 (hp : 20 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 20 (transLenTr ⟨63, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 20 (transLenTr ⟨63, by decide⟩ 20 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 20 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 20 (transLenTr ⟨63, by decide⟩ 20 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_20.D1 (m := 5) from colCertDiv_117_63_20.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 20 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_20.D2 (m := 5) from colCertDiv_117_63_20.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_20_match


theorem leaf_117_63_21 (hp : 21 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 21 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 21 (transLenTr ⟨63, by decide⟩ 21 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 21 (transLenTr ⟨63, by decide⟩ 21 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 21 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 21 (transLenTr ⟨63, by decide⟩ 21 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_21.D1 (m := 5) from colCertDiv_117_63_21.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 21 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_21.D2 (m := 5) from colCertDiv_117_63_21.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_21_match


theorem leaf_117_63_22 (hp : 22 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 22 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 22 (transLenTr ⟨63, by decide⟩ 22 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 22 (transLenTr ⟨63, by decide⟩ 22 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 22 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 22 (transLenTr ⟨63, by decide⟩ 22 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_22.D1 (m := 5) from colCertDiv_117_63_22.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 22 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_22.D2 (m := 5) from colCertDiv_117_63_22.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_22_match


theorem leaf_117_63_23 (hp : 23 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 23 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 23 (transLenTr ⟨63, by decide⟩ 23 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 23 (transLenTr ⟨63, by decide⟩ 23 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 23 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 23 (transLenTr ⟨63, by decide⟩ 23 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_23.D1 (m := 5) from colCertDiv_117_63_23.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 23 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_23.D2 (m := 5) from colCertDiv_117_63_23.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_23_match


theorem leaf_117_63_24 (hp : 24 < (Q2.transData.getD 63 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨63, by decide⟩ : Fin 148)) (colE2 ⟨63, by decide⟩ 24 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨63, by decide⟩ : Fin 148))
        (colE1 ⟨63, by decide⟩ 24 (transLenTr ⟨63, by decide⟩ 24 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨117, by decide⟩ : Fin 148) ⟨63, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨63, by decide⟩ 24 (transLenTr ⟨63, by decide⟩ 24 hp)) T117_63
      hfix117_63 hinj117_63 hcardT117_63
      (fun i => conj_mem_of_fixedPoints _ _ (T117_63 i) (hfix117_63 i) _)
      ⟨117, by decide⟩ ⟨63, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨63, by decide⟩ 24 hp) Q2.T117_63_2 Q2.hfix117_63_2 Q2.hinj117_63_2
      Q2.hcardT117_63_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_63_2 i) (Q2.hfix117_63_2 i) _)
      ?_).symm
  rw [show colData1 (⟨117, by decide⟩ : Fin 148)
        ((colE1 ⟨63, by decide⟩ 24 (transLenTr ⟨63, by decide⟩ 24 hp) : ↥(reps ⟨63, by decide⟩)) : Coordinate 1)
        T117_63 = colFn colCertDiv_117_63_24.D1 (m := 5) from colCertDiv_117_63_24.bind1,
    show colData2 (⟨117, by decide⟩ : Fin 148)
        ((colE2 ⟨63, by decide⟩ 24 hp : ↥(Q2.reps ⟨63, by decide⟩)) : Coordinate 2)
        Q2.T117_63_2 = colFn colCertDiv_117_63_24.D2 (m := 5) from colCertDiv_117_63_24.bind2]
  rw [alnId_117 j hj]
  exact fastcode_of_div ⟨117, by decide⟩ _ _ _
    ((alnId_117 j hj) ▸ Q2.listedAt (⟨117, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨117, by decide⟩ : Fin 148) hj hq).1) colCertDiv_117_63_24_match


theorem leaf_117_64_0 (hp : 0 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 0 (transLenTr ⟨64, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 0 (transLenTr ⟨64, by decide⟩ 0 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 0 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_1 (hp : 1 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 1 (transLenTr ⟨64, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 1 (transLenTr ⟨64, by decide⟩ 1 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 1 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_2 (hp : 2 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 2 (transLenTr ⟨64, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 2 (transLenTr ⟨64, by decide⟩ 2 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 2 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_3 (hp : 3 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 3 (transLenTr ⟨64, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 3 (transLenTr ⟨64, by decide⟩ 3 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 3 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_4 (hp : 4 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 4 (transLenTr ⟨64, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 4 (transLenTr ⟨64, by decide⟩ 4 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 4 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_5 (hp : 5 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 5 (transLenTr ⟨64, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 5 (transLenTr ⟨64, by decide⟩ 5 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 5 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_5.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_6 (hp : 6 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 6 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 6 (transLenTr ⟨64, by decide⟩ 6 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 6 (transLenTr ⟨64, by decide⟩ 6 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 6 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_6.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_7 (hp : 7 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 7 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 7 (transLenTr ⟨64, by decide⟩ 7 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 7 (transLenTr ⟨64, by decide⟩ 7 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 7 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_7.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_8 (hp : 8 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 8 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 8 (transLenTr ⟨64, by decide⟩ 8 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 8 (transLenTr ⟨64, by decide⟩ 8 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 8 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_8.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_9 (hp : 9 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 9 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 9 (transLenTr ⟨64, by decide⟩ 9 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 9 (transLenTr ⟨64, by decide⟩ 9 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 9 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_9.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_10 (hp : 10 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 10 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 10 (transLenTr ⟨64, by decide⟩ 10 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 10 (transLenTr ⟨64, by decide⟩ 10 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 10 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_10.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_11 (hp : 11 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 11 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 11 (transLenTr ⟨64, by decide⟩ 11 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 11 (transLenTr ⟨64, by decide⟩ 11 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 11 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_11.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_12 (hp : 12 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 12 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 12 (transLenTr ⟨64, by decide⟩ 12 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 12 (transLenTr ⟨64, by decide⟩ 12 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 12 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_12.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_13 (hp : 13 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 13 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 13 (transLenTr ⟨64, by decide⟩ 13 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 13 (transLenTr ⟨64, by decide⟩ 13 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 13 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_13.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_14 (hp : 14 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 14 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 14 (transLenTr ⟨64, by decide⟩ 14 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 14 (transLenTr ⟨64, by decide⟩ 14 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 14 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_14.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_15 (hp : 15 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 15 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 15 (transLenTr ⟨64, by decide⟩ 15 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 15 (transLenTr ⟨64, by decide⟩ 15 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 15 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_15.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_16 (hp : 16 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 16 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 16 (transLenTr ⟨64, by decide⟩ 16 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 16 (transLenTr ⟨64, by decide⟩ 16 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 16 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_16.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_17 (hp : 17 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 17 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 17 (transLenTr ⟨64, by decide⟩ 17 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 17 (transLenTr ⟨64, by decide⟩ 17 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 17 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_17.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_18 (hp : 18 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 18 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 18 (transLenTr ⟨64, by decide⟩ 18 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 18 (transLenTr ⟨64, by decide⟩ 18 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 18 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_18.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_19 (hp : 19 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 19 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 19 (transLenTr ⟨64, by decide⟩ 19 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 19 (transLenTr ⟨64, by decide⟩ 19 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 19 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_19.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_20 (hp : 20 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 20 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 20 (transLenTr ⟨64, by decide⟩ 20 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 20 (transLenTr ⟨64, by decide⟩ 20 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 20 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_20.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_21 (hp : 21 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 21 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 21 (transLenTr ⟨64, by decide⟩ 21 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 21 (transLenTr ⟨64, by decide⟩ 21 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 21 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_21.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_22 (hp : 22 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 22 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 22 (transLenTr ⟨64, by decide⟩ 22 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 22 (transLenTr ⟨64, by decide⟩ 22 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 22 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_22.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_23 (hp : 23 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 23 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 23 (transLenTr ⟨64, by decide⟩ 23 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 23 (transLenTr ⟨64, by decide⟩ 23 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 23 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_23.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_24 (hp : 24 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 24 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 24 (transLenTr ⟨64, by decide⟩ 24 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 24 (transLenTr ⟨64, by decide⟩ 24 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 24 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_24.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_25 (hp : 25 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 25 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 25 (transLenTr ⟨64, by decide⟩ 25 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 25 (transLenTr ⟨64, by decide⟩ 25 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 25 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_25.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_30 (hp : 30 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 30 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 30 (transLenTr ⟨64, by decide⟩ 30 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 30 (transLenTr ⟨64, by decide⟩ 30 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 30 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_30.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_35 (hp : 35 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 35 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 35 (transLenTr ⟨64, by decide⟩ 35 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 35 (transLenTr ⟨64, by decide⟩ 35 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 35 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_35.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_40 (hp : 40 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 40 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 40 (transLenTr ⟨64, by decide⟩ 40 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 40 (transLenTr ⟨64, by decide⟩ 40 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 40 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_40.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_45 (hp : 45 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 45 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 45 (transLenTr ⟨64, by decide⟩ 45 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 45 (transLenTr ⟨64, by decide⟩ 45 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 45 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_45.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_50 (hp : 50 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 50 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 50 (transLenTr ⟨64, by decide⟩ 50 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 50 (transLenTr ⟨64, by decide⟩ 50 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 50 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_50.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_55 (hp : 55 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 55 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 55 (transLenTr ⟨64, by decide⟩ 55 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 55 (transLenTr ⟨64, by decide⟩ 55 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 55 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_55.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_60 (hp : 60 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 60 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 60 (transLenTr ⟨64, by decide⟩ 60 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 60 (transLenTr ⟨64, by decide⟩ 60 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 60 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_60.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_65 (hp : 65 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 65 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 65 (transLenTr ⟨64, by decide⟩ 65 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 65 (transLenTr ⟨64, by decide⟩ 65 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 65 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_65.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_70 (hp : 70 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 70 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 70 (transLenTr ⟨64, by decide⟩ 70 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 70 (transLenTr ⟨64, by decide⟩ 70 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 70 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_70.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_75 (hp : 75 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 75 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 75 (transLenTr ⟨64, by decide⟩ 75 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 75 (transLenTr ⟨64, by decide⟩ 75 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 75 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_75.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_80 (hp : 80 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 80 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 80 (transLenTr ⟨64, by decide⟩ 80 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 80 (transLenTr ⟨64, by decide⟩ 80 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 80 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_80.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_85 (hp : 85 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 85 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 85 (transLenTr ⟨64, by decide⟩ 85 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 85 (transLenTr ⟨64, by decide⟩ 85 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 85 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_85.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_90 (hp : 90 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 90 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 90 (transLenTr ⟨64, by decide⟩ 90 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 90 (transLenTr ⟨64, by decide⟩ 90 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 90 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_90.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_95 (hp : 95 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 95 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 95 (transLenTr ⟨64, by decide⟩ 95 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 95 (transLenTr ⟨64, by decide⟩ 95 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 95 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_95.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_100 (hp : 100 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 100 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 100 (transLenTr ⟨64, by decide⟩ 100 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 100 (transLenTr ⟨64, by decide⟩ 100 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 100 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_100.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_105 (hp : 105 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 105 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 105 (transLenTr ⟨64, by decide⟩ 105 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 105 (transLenTr ⟨64, by decide⟩ 105 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 105 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_105.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_110 (hp : 110 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 110 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 110 (transLenTr ⟨64, by decide⟩ 110 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 110 (transLenTr ⟨64, by decide⟩ 110 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 110 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_110.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_115 (hp : 115 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 115 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 115 (transLenTr ⟨64, by decide⟩ 115 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 115 (transLenTr ⟨64, by decide⟩ 115 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 115 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_115.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_64_120 (hp : 120 < (Q2.transData.getD 64 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨64, by decide⟩ : Fin 148)) (colE2 ⟨64, by decide⟩ 120 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨64, by decide⟩ : Fin 148))
        (colE1 ⟨64, by decide⟩ 120 (transLenTr ⟨64, by decide⟩ 120 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨64, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨64, by decide⟩ 120 (transLenTr ⟨64, by decide⟩ 120 hp)) T117_64
      hfix117_64 hinj117_64 hcardT117_64
      (fun i => conj_mem_of_fixedPoints _ _ (T117_64 i) (hfix117_64 i) _)
      ⟨117, by decide⟩ ⟨64, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨64, by decide⟩ 120 hp) Q2.T117_64_2 Q2.hfix117_64_2 Q2.hinj117_64_2
      Q2.hcardT117_64_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_64_2 i) (Q2.hfix117_64_2 i) _)
      colCert_117_64_120.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_0 (hp : 0 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 0 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 0 (transLenTr ⟨80, by decide⟩ 0 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 0 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_0.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_1 (hp : 1 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 1 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 1 (transLenTr ⟨80, by decide⟩ 1 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 1 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_1.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_2 (hp : 2 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 2 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 2 (transLenTr ⟨80, by decide⟩ 2 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 2 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_2.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_3 (hp : 3 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 3 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 3 (transLenTr ⟨80, by decide⟩ 3 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 3 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_3.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_4 (hp : 4 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 4 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 4 (transLenTr ⟨80, by decide⟩ 4 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 4 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_4.hD ?_).symm
  rw [alnId_117 j hj]


theorem leaf_117_80_5 (hp : 5 < (Q2.transData.getD 80 []).length)
    (j : Nat) (hj : j < (repChars.getD 117 []).length)
    (hq : (normIsRep.getD 117 []).getD j false = true) :
    species (Q2.reps (⟨80, by decide⟩ : Fin 148)) (colE2 ⟨80, by decide⟩ 5 hp)
        (rowE2 (⟨117, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨80, by decide⟩ : Fin 148))
        (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp))
        (rowE1 (⟨117, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨117, by decide⟩ : Fin 148) ⟨80, by decide⟩ _
      (validAt ⟨117, by decide⟩ (listedAt ⟨117, by decide⟩ hj))
      (colE1 ⟨80, by decide⟩ 5 (transLenTr ⟨80, by decide⟩ 5 hp)) T117_80
      hfix117_80 hinj117_80 hcardT117_80
      (fun i => conj_mem_of_fixedPoints _ _ (T117_80 i) (hfix117_80 i) _)
      ⟨117, by decide⟩ ⟨80, by decide⟩ _
      (Q2.validAt ⟨117, by decide⟩ (Q2.listedAt ⟨117, by decide⟩
        (alnCheck_rep ⟨117, by decide⟩ hj hq).1))
      (colE2 ⟨80, by decide⟩ 5 hp) Q2.T117_80_2 Q2.hfix117_80_2 Q2.hinj117_80_2
      Q2.hcardT117_80_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T117_80_2 i) (Q2.hfix117_80_2 i) _)
      colCert_117_80_5.hD ?_).symm
  rw [alnId_117 j hj]


end LeanDring.P5Presentation
