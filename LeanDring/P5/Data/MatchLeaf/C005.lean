/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C037
import LeanDring.P5.Data.ColRestCheap.C140
import LeanDring.P5.Data.ColRestCheap.C141
import LeanDring.P5.Data.ColRestCheap.C142
import LeanDring.P5.Data.ColRestCheap.C143
import LeanDring.P5.Data.EntryK.C014
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesDiv.C043
import LeanDring.P5.Data.SpeciesDiv.C044

/-! # Stage-5 leaves, chunk 4 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_55_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T55_43
      hfix55_43 hinj55_43 hcardT55_43
      (fun i => conj_mem_of_fixedPoints _ _ (T55_43 i) (hfix55_43 i) _)
      ⟨55, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T55_43_2 Q2.hfix55_43_2 Q2.hinj55_43_2
      Q2.hcardT55_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_43_2 i) (Q2.hfix55_43_2 i) _)
      colCert_55_43_5.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T55_43
      hfix55_43 hinj55_43 hcardT55_43
      (fun i => conj_mem_of_fixedPoints _ _ (T55_43 i) (hfix55_43 i) _)
      ⟨55, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T55_43_2 Q2.hfix55_43_2 Q2.hinj55_43_2
      Q2.hcardT55_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_43_2 i) (Q2.hfix55_43_2 i) _)
      colCert_55_43_10.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T55_43
      hfix55_43 hinj55_43 hcardT55_43
      (fun i => conj_mem_of_fixedPoints _ _ (T55_43 i) (hfix55_43 i) _)
      ⟨55, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T55_43_2 Q2.hfix55_43_2 Q2.hinj55_43_2
      Q2.hcardT55_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_43_2 i) (Q2.hfix55_43_2 i) _)
      colCert_55_43_15.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T55_43
      hfix55_43 hinj55_43 hcardT55_43
      (fun i => conj_mem_of_fixedPoints _ _ (T55_43 i) (hfix55_43 i) _)
      ⟨55, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T55_43_2 Q2.hfix55_43_2 Q2.hinj55_43_2
      Q2.hcardT55_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_43_2 i) (Q2.hfix55_43_2 i) _)
      colCert_55_43_20.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T55_48
      hfix55_48 hinj55_48 hcardT55_48
      (fun i => conj_mem_of_fixedPoints _ _ (T55_48 i) (hfix55_48 i) _)
      ⟨55, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T55_48_2 Q2.hfix55_48_2 Q2.hinj55_48_2
      Q2.hcardT55_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_48_2 i) (Q2.hfix55_48_2 i) _)
      colCert_55_48_0.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T55_48
      hfix55_48 hinj55_48 hcardT55_48
      (fun i => conj_mem_of_fixedPoints _ _ (T55_48 i) (hfix55_48 i) _)
      ⟨55, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T55_48_2 Q2.hfix55_48_2 Q2.hinj55_48_2
      Q2.hcardT55_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_48_2 i) (Q2.hfix55_48_2 i) _)
      colCert_55_48_1.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T55_48
      hfix55_48 hinj55_48 hcardT55_48
      (fun i => conj_mem_of_fixedPoints _ _ (T55_48 i) (hfix55_48 i) _)
      ⟨55, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T55_48_2 Q2.hfix55_48_2 Q2.hinj55_48_2
      Q2.hcardT55_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_48_2 i) (Q2.hfix55_48_2 i) _)
      colCert_55_48_2.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T55_48
      hfix55_48 hinj55_48 hcardT55_48
      (fun i => conj_mem_of_fixedPoints _ _ (T55_48 i) (hfix55_48 i) _)
      ⟨55, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T55_48_2 Q2.hfix55_48_2 Q2.hinj55_48_2
      Q2.hcardT55_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_48_2 i) (Q2.hfix55_48_2 i) _)
      colCert_55_48_3.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T55_48
      hfix55_48 hinj55_48 hcardT55_48
      (fun i => conj_mem_of_fixedPoints _ _ (T55_48 i) (hfix55_48 i) _)
      ⟨55, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T55_48_2 Q2.hfix55_48_2 Q2.hinj55_48_2
      Q2.hcardT55_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_48_2 i) (Q2.hfix55_48_2 i) _)
      colCert_55_48_4.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T55_48
      hfix55_48 hinj55_48 hcardT55_48
      (fun i => conj_mem_of_fixedPoints _ _ (T55_48 i) (hfix55_48 i) _)
      ⟨55, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T55_48_2 Q2.hfix55_48_2 Q2.hinj55_48_2
      Q2.hcardT55_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_48_2 i) (Q2.hfix55_48_2 i) _)
      colCert_55_48_5.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T55_48
      hfix55_48 hinj55_48 hcardT55_48
      (fun i => conj_mem_of_fixedPoints _ _ (T55_48 i) (hfix55_48 i) _)
      ⟨55, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T55_48_2 Q2.hfix55_48_2 Q2.hinj55_48_2
      Q2.hcardT55_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_48_2 i) (Q2.hfix55_48_2 i) _)
      colCert_55_48_10.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T55_48
      hfix55_48 hinj55_48 hcardT55_48
      (fun i => conj_mem_of_fixedPoints _ _ (T55_48 i) (hfix55_48 i) _)
      ⟨55, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T55_48_2 Q2.hfix55_48_2 Q2.hinj55_48_2
      Q2.hcardT55_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_48_2 i) (Q2.hfix55_48_2 i) _)
      colCert_55_48_15.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T55_48
      hfix55_48 hinj55_48 hcardT55_48
      (fun i => conj_mem_of_fixedPoints _ _ (T55_48 i) (hfix55_48 i) _)
      ⟨55, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T55_48_2 Q2.hfix55_48_2 Q2.hinj55_48_2
      Q2.hcardT55_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_48_2 i) (Q2.hfix55_48_2 i) _)
      colCert_55_48_20.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_0 (hp : 0 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 0 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 0 (transLenTr ⟨55, by decide⟩ 0 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 0 (transLenTr ⟨55, by decide⟩ 0 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 0 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_0.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_1 (hp : 1 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 1 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 1 (transLenTr ⟨55, by decide⟩ 1 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 1 (transLenTr ⟨55, by decide⟩ 1 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 1 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_1.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_2 (hp : 2 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 2 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 2 (transLenTr ⟨55, by decide⟩ 2 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 2 (transLenTr ⟨55, by decide⟩ 2 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 2 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_2.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_3 (hp : 3 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 3 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 3 (transLenTr ⟨55, by decide⟩ 3 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 3 (transLenTr ⟨55, by decide⟩ 3 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 3 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_3.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_4 (hp : 4 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 4 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 4 (transLenTr ⟨55, by decide⟩ 4 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 4 (transLenTr ⟨55, by decide⟩ 4 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 4 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_4.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_5 (hp : 5 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 5 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 5 (transLenTr ⟨55, by decide⟩ 5 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 5 (transLenTr ⟨55, by decide⟩ 5 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 5 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_5.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_6 (hp : 6 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 6 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 6 (transLenTr ⟨55, by decide⟩ 6 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 6 (transLenTr ⟨55, by decide⟩ 6 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 6 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_6.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_7 (hp : 7 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 7 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 7 (transLenTr ⟨55, by decide⟩ 7 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 7 (transLenTr ⟨55, by decide⟩ 7 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 7 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_7.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_8 (hp : 8 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 8 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 8 (transLenTr ⟨55, by decide⟩ 8 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 8 (transLenTr ⟨55, by decide⟩ 8 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 8 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_8.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_9 (hp : 9 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 9 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 9 (transLenTr ⟨55, by decide⟩ 9 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 9 (transLenTr ⟨55, by decide⟩ 9 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 9 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_9.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_10 (hp : 10 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 10 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 10 (transLenTr ⟨55, by decide⟩ 10 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 10 (transLenTr ⟨55, by decide⟩ 10 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 10 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_10.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_11 (hp : 11 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 11 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 11 (transLenTr ⟨55, by decide⟩ 11 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 11 (transLenTr ⟨55, by decide⟩ 11 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 11 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_11.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_12 (hp : 12 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 12 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 12 (transLenTr ⟨55, by decide⟩ 12 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 12 (transLenTr ⟨55, by decide⟩ 12 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 12 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_12.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_13 (hp : 13 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 13 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 13 (transLenTr ⟨55, by decide⟩ 13 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 13 (transLenTr ⟨55, by decide⟩ 13 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 13 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_13.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_14 (hp : 14 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 14 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 14 (transLenTr ⟨55, by decide⟩ 14 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 14 (transLenTr ⟨55, by decide⟩ 14 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 14 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_14.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_15 (hp : 15 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 15 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 15 (transLenTr ⟨55, by decide⟩ 15 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 15 (transLenTr ⟨55, by decide⟩ 15 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 15 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_15.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_16 (hp : 16 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 16 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 16 (transLenTr ⟨55, by decide⟩ 16 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 16 (transLenTr ⟨55, by decide⟩ 16 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 16 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_16.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_17 (hp : 17 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 17 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 17 (transLenTr ⟨55, by decide⟩ 17 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 17 (transLenTr ⟨55, by decide⟩ 17 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 17 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_17.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_18 (hp : 18 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 18 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 18 (transLenTr ⟨55, by decide⟩ 18 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 18 (transLenTr ⟨55, by decide⟩ 18 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 18 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_18.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_19 (hp : 19 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 19 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 19 (transLenTr ⟨55, by decide⟩ 19 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 19 (transLenTr ⟨55, by decide⟩ 19 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 19 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_19.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_20 (hp : 20 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 20 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 20 (transLenTr ⟨55, by decide⟩ 20 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 20 (transLenTr ⟨55, by decide⟩ 20 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 20 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_20.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_21 (hp : 21 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 21 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 21 (transLenTr ⟨55, by decide⟩ 21 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 21 (transLenTr ⟨55, by decide⟩ 21 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 21 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_21.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_22 (hp : 22 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 22 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 22 (transLenTr ⟨55, by decide⟩ 22 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 22 (transLenTr ⟨55, by decide⟩ 22 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 22 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_22.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_23 (hp : 23 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 23 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 23 (transLenTr ⟨55, by decide⟩ 23 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 23 (transLenTr ⟨55, by decide⟩ 23 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 23 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_23.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_55_55_24 (hp : 24 < (Q2.transData.getD 55 []).length)
    (j : Nat) (hj : j < (repChars.getD 55 []).length)
    (hq : (normIsRep.getD 55 []).getD j false = true) :
    species (Q2.reps (⟨55, by decide⟩ : Fin 148)) (colE2 ⟨55, by decide⟩ 24 hp)
        (rowE2 (⟨55, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨55, by decide⟩ : Fin 148))
        (colE1 ⟨55, by decide⟩ 24 (transLenTr ⟨55, by decide⟩ 24 hp))
        (rowE1 (⟨55, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨55, by decide⟩ : Fin 148) ⟨55, by decide⟩ _
      (validAt ⟨55, by decide⟩ (listedAt ⟨55, by decide⟩ hj))
      (colE1 ⟨55, by decide⟩ 24 (transLenTr ⟨55, by decide⟩ 24 hp)) T55_55
      hfix55_55 hinj55_55 hcardT55_55
      (fun i => conj_mem_of_fixedPoints _ _ (T55_55 i) (hfix55_55 i) _)
      ⟨55, by decide⟩ ⟨55, by decide⟩ _
      (Q2.validAt ⟨55, by decide⟩ (Q2.listedAt ⟨55, by decide⟩
        (alnCheck_rep ⟨55, by decide⟩ hj hq).1))
      (colE2 ⟨55, by decide⟩ 24 hp) Q2.T55_55_2 Q2.hfix55_55_2 Q2.hinj55_55_2
      Q2.hcardT55_55_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T55_55_2 i) (Q2.hfix55_55_2 i) _)
      colCert_55_55_24.hD ?_).symm
  rw [alnId_55 j hj]


theorem leaf_56_1_0 (hp : 0 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 0 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 0 (transLenTr ⟨1, by decide⟩ 0 hp)) T56_1
      hfix56_1 hinj56_1 hcardT56_1
      (fun i => conj_mem_of_fixedPoints _ _ (T56_1 i) (hfix56_1 i) _)
      ⟨56, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 0 hp) Q2.T56_1_2 Q2.hfix56_1_2 Q2.hinj56_1_2
      Q2.hcardT56_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_1_2 i) (Q2.hfix56_1_2 i) _)
      colCert_56_1_0.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_1_1 (hp : 1 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 1 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 1 (transLenTr ⟨1, by decide⟩ 1 hp)) T56_1
      hfix56_1 hinj56_1 hcardT56_1
      (fun i => conj_mem_of_fixedPoints _ _ (T56_1 i) (hfix56_1 i) _)
      ⟨56, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 1 hp) Q2.T56_1_2 Q2.hfix56_1_2 Q2.hinj56_1_2
      Q2.hcardT56_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_1_2 i) (Q2.hfix56_1_2 i) _)
      colCert_56_1_1.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_1_2 (hp : 2 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 2 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 2 (transLenTr ⟨1, by decide⟩ 2 hp)) T56_1
      hfix56_1 hinj56_1 hcardT56_1
      (fun i => conj_mem_of_fixedPoints _ _ (T56_1 i) (hfix56_1 i) _)
      ⟨56, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 2 hp) Q2.T56_1_2 Q2.hfix56_1_2 Q2.hinj56_1_2
      Q2.hcardT56_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_1_2 i) (Q2.hfix56_1_2 i) _)
      colCert_56_1_2.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_1_3 (hp : 3 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 3 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 3 (transLenTr ⟨1, by decide⟩ 3 hp)) T56_1
      hfix56_1 hinj56_1 hcardT56_1
      (fun i => conj_mem_of_fixedPoints _ _ (T56_1 i) (hfix56_1 i) _)
      ⟨56, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 3 hp) Q2.T56_1_2 Q2.hfix56_1_2 Q2.hinj56_1_2
      Q2.hcardT56_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_1_2 i) (Q2.hfix56_1_2 i) _)
      colCert_56_1_3.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_1_4 (hp : 4 < (Q2.transData.getD 1 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨1, by decide⟩ : Fin 148)) (colE2 ⟨1, by decide⟩ 4 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨1, by decide⟩ : Fin 148))
        (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨1, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨1, by decide⟩ 4 (transLenTr ⟨1, by decide⟩ 4 hp)) T56_1
      hfix56_1 hinj56_1 hcardT56_1
      (fun i => conj_mem_of_fixedPoints _ _ (T56_1 i) (hfix56_1 i) _)
      ⟨56, by decide⟩ ⟨1, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨1, by decide⟩ 4 hp) Q2.T56_1_2 Q2.hfix56_1_2 Q2.hinj56_1_2
      Q2.hcardT56_1_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_1_2 i) (Q2.hfix56_1_2 i) _)
      colCert_56_1_4.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T56_12
      hfix56_12 hinj56_12 hcardT56_12
      (fun i => conj_mem_of_fixedPoints _ _ (T56_12 i) (hfix56_12 i) _)
      ⟨56, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T56_12_2 Q2.hfix56_12_2 Q2.hinj56_12_2
      Q2.hcardT56_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_12_2 i) (Q2.hfix56_12_2 i) _)
      colCert_56_12_0.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T56_12
      hfix56_12 hinj56_12 hcardT56_12
      (fun i => conj_mem_of_fixedPoints _ _ (T56_12 i) (hfix56_12 i) _)
      ⟨56, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T56_12_2 Q2.hfix56_12_2 Q2.hinj56_12_2
      Q2.hcardT56_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_12_2 i) (Q2.hfix56_12_2 i) _)
      colCert_56_12_1.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T56_12
      hfix56_12 hinj56_12 hcardT56_12
      (fun i => conj_mem_of_fixedPoints _ _ (T56_12 i) (hfix56_12 i) _)
      ⟨56, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T56_12_2 Q2.hfix56_12_2 Q2.hinj56_12_2
      Q2.hcardT56_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_12_2 i) (Q2.hfix56_12_2 i) _)
      colCert_56_12_2.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T56_12
      hfix56_12 hinj56_12 hcardT56_12
      (fun i => conj_mem_of_fixedPoints _ _ (T56_12 i) (hfix56_12 i) _)
      ⟨56, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T56_12_2 Q2.hfix56_12_2 Q2.hinj56_12_2
      Q2.hcardT56_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_12_2 i) (Q2.hfix56_12_2 i) _)
      colCert_56_12_3.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T56_12
      hfix56_12 hinj56_12 hcardT56_12
      (fun i => conj_mem_of_fixedPoints _ _ (T56_12 i) (hfix56_12 i) _)
      ⟨56, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T56_12_2 Q2.hfix56_12_2 Q2.hinj56_12_2
      Q2.hcardT56_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_12_2 i) (Q2.hfix56_12_2 i) _)
      colCert_56_12_4.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_19_0 (hp : 0 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 0 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 0 (transLenTr ⟨19, by decide⟩ 0 hp)) T56_19
      hfix56_19 hinj56_19 hcardT56_19
      (fun i => conj_mem_of_fixedPoints _ _ (T56_19 i) (hfix56_19 i) _)
      ⟨56, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 0 hp) Q2.T56_19_2 Q2.hfix56_19_2 Q2.hinj56_19_2
      Q2.hcardT56_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_19_2 i) (Q2.hfix56_19_2 i) _)
      colCert_56_19_0.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_19_1 (hp : 1 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 1 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 1 (transLenTr ⟨19, by decide⟩ 1 hp)) T56_19
      hfix56_19 hinj56_19 hcardT56_19
      (fun i => conj_mem_of_fixedPoints _ _ (T56_19 i) (hfix56_19 i) _)
      ⟨56, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 1 hp) Q2.T56_19_2 Q2.hfix56_19_2 Q2.hinj56_19_2
      Q2.hcardT56_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_19_2 i) (Q2.hfix56_19_2 i) _)
      colCert_56_19_1.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_19_2 (hp : 2 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 2 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 2 (transLenTr ⟨19, by decide⟩ 2 hp)) T56_19
      hfix56_19 hinj56_19 hcardT56_19
      (fun i => conj_mem_of_fixedPoints _ _ (T56_19 i) (hfix56_19 i) _)
      ⟨56, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 2 hp) Q2.T56_19_2 Q2.hfix56_19_2 Q2.hinj56_19_2
      Q2.hcardT56_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_19_2 i) (Q2.hfix56_19_2 i) _)
      colCert_56_19_2.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_19_3 (hp : 3 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 3 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 3 (transLenTr ⟨19, by decide⟩ 3 hp)) T56_19
      hfix56_19 hinj56_19 hcardT56_19
      (fun i => conj_mem_of_fixedPoints _ _ (T56_19 i) (hfix56_19 i) _)
      ⟨56, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 3 hp) Q2.T56_19_2 Q2.hfix56_19_2 Q2.hinj56_19_2
      Q2.hcardT56_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_19_2 i) (Q2.hfix56_19_2 i) _)
      colCert_56_19_3.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_19_4 (hp : 4 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 4 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 4 (transLenTr ⟨19, by decide⟩ 4 hp)) T56_19
      hfix56_19 hinj56_19 hcardT56_19
      (fun i => conj_mem_of_fixedPoints _ _ (T56_19 i) (hfix56_19 i) _)
      ⟨56, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 4 hp) Q2.T56_19_2 Q2.hfix56_19_2 Q2.hinj56_19_2
      Q2.hcardT56_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_19_2 i) (Q2.hfix56_19_2 i) _)
      colCert_56_19_4.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_19_5 (hp : 5 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 5 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 5 (transLenTr ⟨19, by decide⟩ 5 hp)) T56_19
      hfix56_19 hinj56_19 hcardT56_19
      (fun i => conj_mem_of_fixedPoints _ _ (T56_19 i) (hfix56_19 i) _)
      ⟨56, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 5 hp) Q2.T56_19_2 Q2.hfix56_19_2 Q2.hinj56_19_2
      Q2.hcardT56_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_19_2 i) (Q2.hfix56_19_2 i) _)
      colCert_56_19_5.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_19_10 (hp : 10 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 10 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 10 (transLenTr ⟨19, by decide⟩ 10 hp)) T56_19
      hfix56_19 hinj56_19 hcardT56_19
      (fun i => conj_mem_of_fixedPoints _ _ (T56_19 i) (hfix56_19 i) _)
      ⟨56, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 10 hp) Q2.T56_19_2 Q2.hfix56_19_2 Q2.hinj56_19_2
      Q2.hcardT56_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_19_2 i) (Q2.hfix56_19_2 i) _)
      colCert_56_19_10.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_19_15 (hp : 15 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 15 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 15 (transLenTr ⟨19, by decide⟩ 15 hp)) T56_19
      hfix56_19 hinj56_19 hcardT56_19
      (fun i => conj_mem_of_fixedPoints _ _ (T56_19 i) (hfix56_19 i) _)
      ⟨56, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 15 hp) Q2.T56_19_2 Q2.hfix56_19_2 Q2.hinj56_19_2
      Q2.hcardT56_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_19_2 i) (Q2.hfix56_19_2 i) _)
      colCert_56_19_15.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_19_20 (hp : 20 < (Q2.transData.getD 19 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨19, by decide⟩ : Fin 148)) (colE2 ⟨19, by decide⟩ 20 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨19, by decide⟩ : Fin 148))
        (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨19, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨19, by decide⟩ 20 (transLenTr ⟨19, by decide⟩ 20 hp)) T56_19
      hfix56_19 hinj56_19 hcardT56_19
      (fun i => conj_mem_of_fixedPoints _ _ (T56_19 i) (hfix56_19 i) _)
      ⟨56, by decide⟩ ⟨19, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨19, by decide⟩ 20 hp) Q2.T56_19_2 Q2.hfix56_19_2 Q2.hinj56_19_2
      Q2.hcardT56_19_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_19_2 i) (Q2.hfix56_19_2 i) _)
      colCert_56_19_20.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T56_28
      hfix56_28 hinj56_28 hcardT56_28
      (fun i => conj_mem_of_fixedPoints _ _ (T56_28 i) (hfix56_28 i) _)
      ⟨56, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T56_28_2 Q2.hfix56_28_2 Q2.hinj56_28_2
      Q2.hcardT56_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_28_2 i) (Q2.hfix56_28_2 i) _)
      colCert_56_28_0.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T56_28
      hfix56_28 hinj56_28 hcardT56_28
      (fun i => conj_mem_of_fixedPoints _ _ (T56_28 i) (hfix56_28 i) _)
      ⟨56, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T56_28_2 Q2.hfix56_28_2 Q2.hinj56_28_2
      Q2.hcardT56_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_28_2 i) (Q2.hfix56_28_2 i) _)
      colCert_56_28_1.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T56_28
      hfix56_28 hinj56_28 hcardT56_28
      (fun i => conj_mem_of_fixedPoints _ _ (T56_28 i) (hfix56_28 i) _)
      ⟨56, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T56_28_2 Q2.hfix56_28_2 Q2.hinj56_28_2
      Q2.hcardT56_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_28_2 i) (Q2.hfix56_28_2 i) _)
      colCert_56_28_2.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T56_28
      hfix56_28 hinj56_28 hcardT56_28
      (fun i => conj_mem_of_fixedPoints _ _ (T56_28 i) (hfix56_28 i) _)
      ⟨56, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T56_28_2 Q2.hfix56_28_2 Q2.hinj56_28_2
      Q2.hcardT56_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_28_2 i) (Q2.hfix56_28_2 i) _)
      colCert_56_28_3.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T56_28
      hfix56_28 hinj56_28 hcardT56_28
      (fun i => conj_mem_of_fixedPoints _ _ (T56_28 i) (hfix56_28 i) _)
      ⟨56, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T56_28_2 Q2.hfix56_28_2 Q2.hinj56_28_2
      Q2.hcardT56_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_28_2 i) (Q2.hfix56_28_2 i) _)
      colCert_56_28_4.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T56_28
      hfix56_28 hinj56_28 hcardT56_28
      (fun i => conj_mem_of_fixedPoints _ _ (T56_28 i) (hfix56_28 i) _)
      ⟨56, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T56_28_2 Q2.hfix56_28_2 Q2.hinj56_28_2
      Q2.hcardT56_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_28_2 i) (Q2.hfix56_28_2 i) _)
      colCert_56_28_5.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T56_28
      hfix56_28 hinj56_28 hcardT56_28
      (fun i => conj_mem_of_fixedPoints _ _ (T56_28 i) (hfix56_28 i) _)
      ⟨56, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T56_28_2 Q2.hfix56_28_2 Q2.hinj56_28_2
      Q2.hcardT56_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_28_2 i) (Q2.hfix56_28_2 i) _)
      colCert_56_28_10.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T56_28
      hfix56_28 hinj56_28 hcardT56_28
      (fun i => conj_mem_of_fixedPoints _ _ (T56_28 i) (hfix56_28 i) _)
      ⟨56, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T56_28_2 Q2.hfix56_28_2 Q2.hinj56_28_2
      Q2.hcardT56_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_28_2 i) (Q2.hfix56_28_2 i) _)
      colCert_56_28_15.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T56_28
      hfix56_28 hinj56_28 hcardT56_28
      (fun i => conj_mem_of_fixedPoints _ _ (T56_28 i) (hfix56_28 i) _)
      ⟨56, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T56_28_2 Q2.hfix56_28_2 Q2.hinj56_28_2
      Q2.hcardT56_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_28_2 i) (Q2.hfix56_28_2 i) _)
      colCert_56_28_20.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T56_33
      hfix56_33 hinj56_33 hcardT56_33
      (fun i => conj_mem_of_fixedPoints _ _ (T56_33 i) (hfix56_33 i) _)
      ⟨56, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T56_33_2 Q2.hfix56_33_2 Q2.hinj56_33_2
      Q2.hcardT56_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_33_2 i) (Q2.hfix56_33_2 i) _)
      colCert_56_33_0.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T56_33
      hfix56_33 hinj56_33 hcardT56_33
      (fun i => conj_mem_of_fixedPoints _ _ (T56_33 i) (hfix56_33 i) _)
      ⟨56, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T56_33_2 Q2.hfix56_33_2 Q2.hinj56_33_2
      Q2.hcardT56_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_33_2 i) (Q2.hfix56_33_2 i) _)
      colCert_56_33_1.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T56_33
      hfix56_33 hinj56_33 hcardT56_33
      (fun i => conj_mem_of_fixedPoints _ _ (T56_33 i) (hfix56_33 i) _)
      ⟨56, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T56_33_2 Q2.hfix56_33_2 Q2.hinj56_33_2
      Q2.hcardT56_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_33_2 i) (Q2.hfix56_33_2 i) _)
      colCert_56_33_2.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T56_33
      hfix56_33 hinj56_33 hcardT56_33
      (fun i => conj_mem_of_fixedPoints _ _ (T56_33 i) (hfix56_33 i) _)
      ⟨56, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T56_33_2 Q2.hfix56_33_2 Q2.hinj56_33_2
      Q2.hcardT56_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_33_2 i) (Q2.hfix56_33_2 i) _)
      colCert_56_33_3.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T56_33
      hfix56_33 hinj56_33 hcardT56_33
      (fun i => conj_mem_of_fixedPoints _ _ (T56_33 i) (hfix56_33 i) _)
      ⟨56, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T56_33_2 Q2.hfix56_33_2 Q2.hinj56_33_2
      Q2.hcardT56_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_33_2 i) (Q2.hfix56_33_2 i) _)
      colCert_56_33_4.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T56_33
      hfix56_33 hinj56_33 hcardT56_33
      (fun i => conj_mem_of_fixedPoints _ _ (T56_33 i) (hfix56_33 i) _)
      ⟨56, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T56_33_2 Q2.hfix56_33_2 Q2.hinj56_33_2
      Q2.hcardT56_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_33_2 i) (Q2.hfix56_33_2 i) _)
      colCert_56_33_5.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T56_33
      hfix56_33 hinj56_33 hcardT56_33
      (fun i => conj_mem_of_fixedPoints _ _ (T56_33 i) (hfix56_33 i) _)
      ⟨56, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T56_33_2 Q2.hfix56_33_2 Q2.hinj56_33_2
      Q2.hcardT56_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_33_2 i) (Q2.hfix56_33_2 i) _)
      colCert_56_33_10.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T56_33
      hfix56_33 hinj56_33 hcardT56_33
      (fun i => conj_mem_of_fixedPoints _ _ (T56_33 i) (hfix56_33 i) _)
      ⟨56, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T56_33_2 Q2.hfix56_33_2 Q2.hinj56_33_2
      Q2.hcardT56_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_33_2 i) (Q2.hfix56_33_2 i) _)
      colCert_56_33_15.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T56_33
      hfix56_33 hinj56_33 hcardT56_33
      (fun i => conj_mem_of_fixedPoints _ _ (T56_33 i) (hfix56_33 i) _)
      ⟨56, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T56_33_2 Q2.hfix56_33_2 Q2.hinj56_33_2
      Q2.hcardT56_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_33_2 i) (Q2.hfix56_33_2 i) _)
      colCert_56_33_20.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T56_38
      hfix56_38 hinj56_38 hcardT56_38
      (fun i => conj_mem_of_fixedPoints _ _ (T56_38 i) (hfix56_38 i) _)
      ⟨56, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T56_38_2 Q2.hfix56_38_2 Q2.hinj56_38_2
      Q2.hcardT56_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_38_2 i) (Q2.hfix56_38_2 i) _)
      colCert_56_38_0.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T56_38
      hfix56_38 hinj56_38 hcardT56_38
      (fun i => conj_mem_of_fixedPoints _ _ (T56_38 i) (hfix56_38 i) _)
      ⟨56, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T56_38_2 Q2.hfix56_38_2 Q2.hinj56_38_2
      Q2.hcardT56_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_38_2 i) (Q2.hfix56_38_2 i) _)
      colCert_56_38_1.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T56_38
      hfix56_38 hinj56_38 hcardT56_38
      (fun i => conj_mem_of_fixedPoints _ _ (T56_38 i) (hfix56_38 i) _)
      ⟨56, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T56_38_2 Q2.hfix56_38_2 Q2.hinj56_38_2
      Q2.hcardT56_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_38_2 i) (Q2.hfix56_38_2 i) _)
      colCert_56_38_2.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T56_38
      hfix56_38 hinj56_38 hcardT56_38
      (fun i => conj_mem_of_fixedPoints _ _ (T56_38 i) (hfix56_38 i) _)
      ⟨56, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T56_38_2 Q2.hfix56_38_2 Q2.hinj56_38_2
      Q2.hcardT56_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_38_2 i) (Q2.hfix56_38_2 i) _)
      colCert_56_38_3.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T56_38
      hfix56_38 hinj56_38 hcardT56_38
      (fun i => conj_mem_of_fixedPoints _ _ (T56_38 i) (hfix56_38 i) _)
      ⟨56, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T56_38_2 Q2.hfix56_38_2 Q2.hinj56_38_2
      Q2.hcardT56_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_38_2 i) (Q2.hfix56_38_2 i) _)
      colCert_56_38_4.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T56_38
      hfix56_38 hinj56_38 hcardT56_38
      (fun i => conj_mem_of_fixedPoints _ _ (T56_38 i) (hfix56_38 i) _)
      ⟨56, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T56_38_2 Q2.hfix56_38_2 Q2.hinj56_38_2
      Q2.hcardT56_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_38_2 i) (Q2.hfix56_38_2 i) _)
      colCert_56_38_5.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T56_38
      hfix56_38 hinj56_38 hcardT56_38
      (fun i => conj_mem_of_fixedPoints _ _ (T56_38 i) (hfix56_38 i) _)
      ⟨56, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T56_38_2 Q2.hfix56_38_2 Q2.hinj56_38_2
      Q2.hcardT56_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_38_2 i) (Q2.hfix56_38_2 i) _)
      colCert_56_38_10.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T56_38
      hfix56_38 hinj56_38 hcardT56_38
      (fun i => conj_mem_of_fixedPoints _ _ (T56_38 i) (hfix56_38 i) _)
      ⟨56, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T56_38_2 Q2.hfix56_38_2 Q2.hinj56_38_2
      Q2.hcardT56_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_38_2 i) (Q2.hfix56_38_2 i) _)
      colCert_56_38_15.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T56_38
      hfix56_38 hinj56_38 hcardT56_38
      (fun i => conj_mem_of_fixedPoints _ _ (T56_38 i) (hfix56_38 i) _)
      ⟨56, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T56_38_2 Q2.hfix56_38_2 Q2.hinj56_38_2
      Q2.hcardT56_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_38_2 i) (Q2.hfix56_38_2 i) _)
      colCert_56_38_20.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T56_43
      hfix56_43 hinj56_43 hcardT56_43
      (fun i => conj_mem_of_fixedPoints _ _ (T56_43 i) (hfix56_43 i) _)
      ⟨56, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T56_43_2 Q2.hfix56_43_2 Q2.hinj56_43_2
      Q2.hcardT56_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_43_2 i) (Q2.hfix56_43_2 i) _)
      colCert_56_43_0.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T56_43
      hfix56_43 hinj56_43 hcardT56_43
      (fun i => conj_mem_of_fixedPoints _ _ (T56_43 i) (hfix56_43 i) _)
      ⟨56, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T56_43_2 Q2.hfix56_43_2 Q2.hinj56_43_2
      Q2.hcardT56_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_43_2 i) (Q2.hfix56_43_2 i) _)
      colCert_56_43_1.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T56_43
      hfix56_43 hinj56_43 hcardT56_43
      (fun i => conj_mem_of_fixedPoints _ _ (T56_43 i) (hfix56_43 i) _)
      ⟨56, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T56_43_2 Q2.hfix56_43_2 Q2.hinj56_43_2
      Q2.hcardT56_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_43_2 i) (Q2.hfix56_43_2 i) _)
      colCert_56_43_2.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T56_43
      hfix56_43 hinj56_43 hcardT56_43
      (fun i => conj_mem_of_fixedPoints _ _ (T56_43 i) (hfix56_43 i) _)
      ⟨56, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T56_43_2 Q2.hfix56_43_2 Q2.hinj56_43_2
      Q2.hcardT56_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_43_2 i) (Q2.hfix56_43_2 i) _)
      colCert_56_43_3.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T56_43
      hfix56_43 hinj56_43 hcardT56_43
      (fun i => conj_mem_of_fixedPoints _ _ (T56_43 i) (hfix56_43 i) _)
      ⟨56, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T56_43_2 Q2.hfix56_43_2 Q2.hinj56_43_2
      Q2.hcardT56_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_43_2 i) (Q2.hfix56_43_2 i) _)
      colCert_56_43_4.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T56_43
      hfix56_43 hinj56_43 hcardT56_43
      (fun i => conj_mem_of_fixedPoints _ _ (T56_43 i) (hfix56_43 i) _)
      ⟨56, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T56_43_2 Q2.hfix56_43_2 Q2.hinj56_43_2
      Q2.hcardT56_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_43_2 i) (Q2.hfix56_43_2 i) _)
      colCert_56_43_5.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T56_43
      hfix56_43 hinj56_43 hcardT56_43
      (fun i => conj_mem_of_fixedPoints _ _ (T56_43 i) (hfix56_43 i) _)
      ⟨56, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T56_43_2 Q2.hfix56_43_2 Q2.hinj56_43_2
      Q2.hcardT56_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_43_2 i) (Q2.hfix56_43_2 i) _)
      colCert_56_43_10.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T56_43
      hfix56_43 hinj56_43 hcardT56_43
      (fun i => conj_mem_of_fixedPoints _ _ (T56_43 i) (hfix56_43 i) _)
      ⟨56, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T56_43_2 Q2.hfix56_43_2 Q2.hinj56_43_2
      Q2.hcardT56_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_43_2 i) (Q2.hfix56_43_2 i) _)
      colCert_56_43_15.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T56_43
      hfix56_43 hinj56_43 hcardT56_43
      (fun i => conj_mem_of_fixedPoints _ _ (T56_43 i) (hfix56_43 i) _)
      ⟨56, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T56_43_2 Q2.hfix56_43_2 Q2.hinj56_43_2
      Q2.hcardT56_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_43_2 i) (Q2.hfix56_43_2 i) _)
      colCert_56_43_20.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T56_48
      hfix56_48 hinj56_48 hcardT56_48
      (fun i => conj_mem_of_fixedPoints _ _ (T56_48 i) (hfix56_48 i) _)
      ⟨56, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T56_48_2 Q2.hfix56_48_2 Q2.hinj56_48_2
      Q2.hcardT56_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_48_2 i) (Q2.hfix56_48_2 i) _)
      colCert_56_48_0.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T56_48
      hfix56_48 hinj56_48 hcardT56_48
      (fun i => conj_mem_of_fixedPoints _ _ (T56_48 i) (hfix56_48 i) _)
      ⟨56, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T56_48_2 Q2.hfix56_48_2 Q2.hinj56_48_2
      Q2.hcardT56_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_48_2 i) (Q2.hfix56_48_2 i) _)
      colCert_56_48_1.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T56_48
      hfix56_48 hinj56_48 hcardT56_48
      (fun i => conj_mem_of_fixedPoints _ _ (T56_48 i) (hfix56_48 i) _)
      ⟨56, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T56_48_2 Q2.hfix56_48_2 Q2.hinj56_48_2
      Q2.hcardT56_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_48_2 i) (Q2.hfix56_48_2 i) _)
      colCert_56_48_2.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T56_48
      hfix56_48 hinj56_48 hcardT56_48
      (fun i => conj_mem_of_fixedPoints _ _ (T56_48 i) (hfix56_48 i) _)
      ⟨56, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T56_48_2 Q2.hfix56_48_2 Q2.hinj56_48_2
      Q2.hcardT56_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_48_2 i) (Q2.hfix56_48_2 i) _)
      colCert_56_48_3.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T56_48
      hfix56_48 hinj56_48 hcardT56_48
      (fun i => conj_mem_of_fixedPoints _ _ (T56_48 i) (hfix56_48 i) _)
      ⟨56, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T56_48_2 Q2.hfix56_48_2 Q2.hinj56_48_2
      Q2.hcardT56_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_48_2 i) (Q2.hfix56_48_2 i) _)
      colCert_56_48_4.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T56_48
      hfix56_48 hinj56_48 hcardT56_48
      (fun i => conj_mem_of_fixedPoints _ _ (T56_48 i) (hfix56_48 i) _)
      ⟨56, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T56_48_2 Q2.hfix56_48_2 Q2.hinj56_48_2
      Q2.hcardT56_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_48_2 i) (Q2.hfix56_48_2 i) _)
      colCert_56_48_5.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T56_48
      hfix56_48 hinj56_48 hcardT56_48
      (fun i => conj_mem_of_fixedPoints _ _ (T56_48 i) (hfix56_48 i) _)
      ⟨56, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T56_48_2 Q2.hfix56_48_2 Q2.hinj56_48_2
      Q2.hcardT56_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_48_2 i) (Q2.hfix56_48_2 i) _)
      colCert_56_48_10.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T56_48
      hfix56_48 hinj56_48 hcardT56_48
      (fun i => conj_mem_of_fixedPoints _ _ (T56_48 i) (hfix56_48 i) _)
      ⟨56, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T56_48_2 Q2.hfix56_48_2 Q2.hinj56_48_2
      Q2.hcardT56_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_48_2 i) (Q2.hfix56_48_2 i) _)
      colCert_56_48_15.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T56_48
      hfix56_48 hinj56_48 hcardT56_48
      (fun i => conj_mem_of_fixedPoints _ _ (T56_48 i) (hfix56_48 i) _)
      ⟨56, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T56_48_2 Q2.hfix56_48_2 Q2.hinj56_48_2
      Q2.hcardT56_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_48_2 i) (Q2.hfix56_48_2 i) _)
      colCert_56_48_20.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_0 (hp : 0 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 0 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 0 (transLenTr ⟨56, by decide⟩ 0 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 0 (transLenTr ⟨56, by decide⟩ 0 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 0 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_0.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_1 (hp : 1 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 1 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 1 (transLenTr ⟨56, by decide⟩ 1 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 1 (transLenTr ⟨56, by decide⟩ 1 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 1 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_1.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_2 (hp : 2 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 2 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 2 (transLenTr ⟨56, by decide⟩ 2 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 2 (transLenTr ⟨56, by decide⟩ 2 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 2 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_2.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_3 (hp : 3 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 3 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 3 (transLenTr ⟨56, by decide⟩ 3 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 3 (transLenTr ⟨56, by decide⟩ 3 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 3 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_3.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_4 (hp : 4 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 4 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 4 (transLenTr ⟨56, by decide⟩ 4 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 4 (transLenTr ⟨56, by decide⟩ 4 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 4 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_4.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_5 (hp : 5 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 5 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 5 (transLenTr ⟨56, by decide⟩ 5 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 5 (transLenTr ⟨56, by decide⟩ 5 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 5 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_5.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_6 (hp : 6 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 6 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 6 (transLenTr ⟨56, by decide⟩ 6 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 6 (transLenTr ⟨56, by decide⟩ 6 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 6 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_6.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_7 (hp : 7 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 7 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 7 (transLenTr ⟨56, by decide⟩ 7 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 7 (transLenTr ⟨56, by decide⟩ 7 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 7 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_7.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_8 (hp : 8 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 8 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 8 (transLenTr ⟨56, by decide⟩ 8 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 8 (transLenTr ⟨56, by decide⟩ 8 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 8 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_8.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_9 (hp : 9 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 9 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 9 (transLenTr ⟨56, by decide⟩ 9 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 9 (transLenTr ⟨56, by decide⟩ 9 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 9 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_9.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_10 (hp : 10 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 10 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 10 (transLenTr ⟨56, by decide⟩ 10 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 10 (transLenTr ⟨56, by decide⟩ 10 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 10 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_10.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_11 (hp : 11 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 11 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 11 (transLenTr ⟨56, by decide⟩ 11 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 11 (transLenTr ⟨56, by decide⟩ 11 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 11 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_11.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_12 (hp : 12 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 12 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 12 (transLenTr ⟨56, by decide⟩ 12 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 12 (transLenTr ⟨56, by decide⟩ 12 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 12 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_12.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_13 (hp : 13 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 13 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 13 (transLenTr ⟨56, by decide⟩ 13 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 13 (transLenTr ⟨56, by decide⟩ 13 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 13 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_13.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_14 (hp : 14 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 14 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 14 (transLenTr ⟨56, by decide⟩ 14 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 14 (transLenTr ⟨56, by decide⟩ 14 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 14 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_14.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_15 (hp : 15 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 15 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 15 (transLenTr ⟨56, by decide⟩ 15 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 15 (transLenTr ⟨56, by decide⟩ 15 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 15 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_15.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_16 (hp : 16 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 16 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 16 (transLenTr ⟨56, by decide⟩ 16 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 16 (transLenTr ⟨56, by decide⟩ 16 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 16 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_16.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_17 (hp : 17 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 17 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 17 (transLenTr ⟨56, by decide⟩ 17 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 17 (transLenTr ⟨56, by decide⟩ 17 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 17 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_17.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_18 (hp : 18 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 18 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 18 (transLenTr ⟨56, by decide⟩ 18 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 18 (transLenTr ⟨56, by decide⟩ 18 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 18 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_18.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_19 (hp : 19 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 19 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 19 (transLenTr ⟨56, by decide⟩ 19 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 19 (transLenTr ⟨56, by decide⟩ 19 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 19 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_19.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_20 (hp : 20 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 20 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 20 (transLenTr ⟨56, by decide⟩ 20 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 20 (transLenTr ⟨56, by decide⟩ 20 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 20 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_20.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_21 (hp : 21 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 21 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 21 (transLenTr ⟨56, by decide⟩ 21 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 21 (transLenTr ⟨56, by decide⟩ 21 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 21 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_21.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_22 (hp : 22 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 22 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 22 (transLenTr ⟨56, by decide⟩ 22 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 22 (transLenTr ⟨56, by decide⟩ 22 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 22 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_22.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_23 (hp : 23 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 23 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 23 (transLenTr ⟨56, by decide⟩ 23 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 23 (transLenTr ⟨56, by decide⟩ 23 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 23 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_23.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_56_56_24 (hp : 24 < (Q2.transData.getD 56 []).length)
    (j : Nat) (hj : j < (repChars.getD 56 []).length)
    (hq : (normIsRep.getD 56 []).getD j false = true) :
    species (Q2.reps (⟨56, by decide⟩ : Fin 148)) (colE2 ⟨56, by decide⟩ 24 hp)
        (rowE2 (⟨56, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨56, by decide⟩ : Fin 148))
        (colE1 ⟨56, by decide⟩ 24 (transLenTr ⟨56, by decide⟩ 24 hp))
        (rowE1 (⟨56, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨56, by decide⟩ : Fin 148) ⟨56, by decide⟩ _
      (validAt ⟨56, by decide⟩ (listedAt ⟨56, by decide⟩ hj))
      (colE1 ⟨56, by decide⟩ 24 (transLenTr ⟨56, by decide⟩ 24 hp)) T56_56
      hfix56_56 hinj56_56 hcardT56_56
      (fun i => conj_mem_of_fixedPoints _ _ (T56_56 i) (hfix56_56 i) _)
      ⟨56, by decide⟩ ⟨56, by decide⟩ _
      (Q2.validAt ⟨56, by decide⟩ (Q2.listedAt ⟨56, by decide⟩
        (alnCheck_rep ⟨56, by decide⟩ hj hq).1))
      (colE2 ⟨56, by decide⟩ 24 hp) Q2.T56_56_2 Q2.hfix56_56_2 Q2.hinj56_56_2
      Q2.hcardT56_56_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T56_56_2 i) (Q2.hfix56_56_2 i) _)
      colCert_56_56_24.hD ?_).symm
  rw [alnId_56 j hj]


theorem leaf_57_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T57_7
      hfix57_7 hinj57_7 hcardT57_7
      (fun i => conj_mem_of_fixedPoints _ _ (T57_7 i) (hfix57_7 i) _)
      ⟨57, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T57_7_2 Q2.hfix57_7_2 Q2.hinj57_7_2
      Q2.hcardT57_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_7_2 i) (Q2.hfix57_7_2 i) _)
      colCert_57_7_0.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T57_7
      hfix57_7 hinj57_7 hcardT57_7
      (fun i => conj_mem_of_fixedPoints _ _ (T57_7 i) (hfix57_7 i) _)
      ⟨57, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T57_7_2 Q2.hfix57_7_2 Q2.hinj57_7_2
      Q2.hcardT57_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_7_2 i) (Q2.hfix57_7_2 i) _)
      colCert_57_7_1.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T57_7
      hfix57_7 hinj57_7 hcardT57_7
      (fun i => conj_mem_of_fixedPoints _ _ (T57_7 i) (hfix57_7 i) _)
      ⟨57, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T57_7_2 Q2.hfix57_7_2 Q2.hinj57_7_2
      Q2.hcardT57_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_7_2 i) (Q2.hfix57_7_2 i) _)
      colCert_57_7_2.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T57_7
      hfix57_7 hinj57_7 hcardT57_7
      (fun i => conj_mem_of_fixedPoints _ _ (T57_7 i) (hfix57_7 i) _)
      ⟨57, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T57_7_2 Q2.hfix57_7_2 Q2.hinj57_7_2
      Q2.hcardT57_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_7_2 i) (Q2.hfix57_7_2 i) _)
      colCert_57_7_3.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T57_7
      hfix57_7 hinj57_7 hcardT57_7
      (fun i => conj_mem_of_fixedPoints _ _ (T57_7 i) (hfix57_7 i) _)
      ⟨57, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T57_7_2 Q2.hfix57_7_2 Q2.hinj57_7_2
      Q2.hcardT57_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_7_2 i) (Q2.hfix57_7_2 i) _)
      colCert_57_7_4.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T57_12
      hfix57_12 hinj57_12 hcardT57_12
      (fun i => conj_mem_of_fixedPoints _ _ (T57_12 i) (hfix57_12 i) _)
      ⟨57, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T57_12_2 Q2.hfix57_12_2 Q2.hinj57_12_2
      Q2.hcardT57_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_12_2 i) (Q2.hfix57_12_2 i) _)
      colCert_57_12_0.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T57_12
      hfix57_12 hinj57_12 hcardT57_12
      (fun i => conj_mem_of_fixedPoints _ _ (T57_12 i) (hfix57_12 i) _)
      ⟨57, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T57_12_2 Q2.hfix57_12_2 Q2.hinj57_12_2
      Q2.hcardT57_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_12_2 i) (Q2.hfix57_12_2 i) _)
      colCert_57_12_1.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T57_12
      hfix57_12 hinj57_12 hcardT57_12
      (fun i => conj_mem_of_fixedPoints _ _ (T57_12 i) (hfix57_12 i) _)
      ⟨57, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T57_12_2 Q2.hfix57_12_2 Q2.hinj57_12_2
      Q2.hcardT57_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_12_2 i) (Q2.hfix57_12_2 i) _)
      colCert_57_12_2.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T57_12
      hfix57_12 hinj57_12 hcardT57_12
      (fun i => conj_mem_of_fixedPoints _ _ (T57_12 i) (hfix57_12 i) _)
      ⟨57, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T57_12_2 Q2.hfix57_12_2 Q2.hinj57_12_2
      Q2.hcardT57_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_12_2 i) (Q2.hfix57_12_2 i) _)
      colCert_57_12_3.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T57_12
      hfix57_12 hinj57_12 hcardT57_12
      (fun i => conj_mem_of_fixedPoints _ _ (T57_12 i) (hfix57_12 i) _)
      ⟨57, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T57_12_2 Q2.hfix57_12_2 Q2.hinj57_12_2
      Q2.hcardT57_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_12_2 i) (Q2.hfix57_12_2 i) _)
      colCert_57_12_4.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T57_25
      hfix57_25 hinj57_25 hcardT57_25
      (fun i => conj_mem_of_fixedPoints _ _ (T57_25 i) (hfix57_25 i) _)
      ⟨57, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T57_25_2 Q2.hfix57_25_2 Q2.hinj57_25_2
      Q2.hcardT57_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_25_2 i) (Q2.hfix57_25_2 i) _)
      colCert_57_25_0.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T57_25
      hfix57_25 hinj57_25 hcardT57_25
      (fun i => conj_mem_of_fixedPoints _ _ (T57_25 i) (hfix57_25 i) _)
      ⟨57, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T57_25_2 Q2.hfix57_25_2 Q2.hinj57_25_2
      Q2.hcardT57_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_25_2 i) (Q2.hfix57_25_2 i) _)
      colCert_57_25_1.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T57_25
      hfix57_25 hinj57_25 hcardT57_25
      (fun i => conj_mem_of_fixedPoints _ _ (T57_25 i) (hfix57_25 i) _)
      ⟨57, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T57_25_2 Q2.hfix57_25_2 Q2.hinj57_25_2
      Q2.hcardT57_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_25_2 i) (Q2.hfix57_25_2 i) _)
      colCert_57_25_2.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T57_25
      hfix57_25 hinj57_25 hcardT57_25
      (fun i => conj_mem_of_fixedPoints _ _ (T57_25 i) (hfix57_25 i) _)
      ⟨57, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T57_25_2 Q2.hfix57_25_2 Q2.hinj57_25_2
      Q2.hcardT57_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_25_2 i) (Q2.hfix57_25_2 i) _)
      colCert_57_25_3.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T57_25
      hfix57_25 hinj57_25 hcardT57_25
      (fun i => conj_mem_of_fixedPoints _ _ (T57_25 i) (hfix57_25 i) _)
      ⟨57, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T57_25_2 Q2.hfix57_25_2 Q2.hinj57_25_2
      Q2.hcardT57_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_25_2 i) (Q2.hfix57_25_2 i) _)
      colCert_57_25_4.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T57_25
      hfix57_25 hinj57_25 hcardT57_25
      (fun i => conj_mem_of_fixedPoints _ _ (T57_25 i) (hfix57_25 i) _)
      ⟨57, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T57_25_2 Q2.hfix57_25_2 Q2.hinj57_25_2
      Q2.hcardT57_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_25_2 i) (Q2.hfix57_25_2 i) _)
      colCert_57_25_5.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T57_25
      hfix57_25 hinj57_25 hcardT57_25
      (fun i => conj_mem_of_fixedPoints _ _ (T57_25 i) (hfix57_25 i) _)
      ⟨57, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T57_25_2 Q2.hfix57_25_2 Q2.hinj57_25_2
      Q2.hcardT57_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_25_2 i) (Q2.hfix57_25_2 i) _)
      colCert_57_25_10.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T57_25
      hfix57_25 hinj57_25 hcardT57_25
      (fun i => conj_mem_of_fixedPoints _ _ (T57_25 i) (hfix57_25 i) _)
      ⟨57, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T57_25_2 Q2.hfix57_25_2 Q2.hinj57_25_2
      Q2.hcardT57_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_25_2 i) (Q2.hfix57_25_2 i) _)
      colCert_57_25_15.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T57_25
      hfix57_25 hinj57_25 hcardT57_25
      (fun i => conj_mem_of_fixedPoints _ _ (T57_25 i) (hfix57_25 i) _)
      ⟨57, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T57_25_2 Q2.hfix57_25_2 Q2.hinj57_25_2
      Q2.hcardT57_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_25_2 i) (Q2.hfix57_25_2 i) _)
      colCert_57_25_20.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T57_28
      hfix57_28 hinj57_28 hcardT57_28
      (fun i => conj_mem_of_fixedPoints _ _ (T57_28 i) (hfix57_28 i) _)
      ⟨57, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T57_28_2 Q2.hfix57_28_2 Q2.hinj57_28_2
      Q2.hcardT57_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_28_2 i) (Q2.hfix57_28_2 i) _)
      colCert_57_28_0.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T57_28
      hfix57_28 hinj57_28 hcardT57_28
      (fun i => conj_mem_of_fixedPoints _ _ (T57_28 i) (hfix57_28 i) _)
      ⟨57, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T57_28_2 Q2.hfix57_28_2 Q2.hinj57_28_2
      Q2.hcardT57_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_28_2 i) (Q2.hfix57_28_2 i) _)
      colCert_57_28_1.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T57_28
      hfix57_28 hinj57_28 hcardT57_28
      (fun i => conj_mem_of_fixedPoints _ _ (T57_28 i) (hfix57_28 i) _)
      ⟨57, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T57_28_2 Q2.hfix57_28_2 Q2.hinj57_28_2
      Q2.hcardT57_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_28_2 i) (Q2.hfix57_28_2 i) _)
      colCert_57_28_2.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T57_28
      hfix57_28 hinj57_28 hcardT57_28
      (fun i => conj_mem_of_fixedPoints _ _ (T57_28 i) (hfix57_28 i) _)
      ⟨57, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T57_28_2 Q2.hfix57_28_2 Q2.hinj57_28_2
      Q2.hcardT57_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_28_2 i) (Q2.hfix57_28_2 i) _)
      colCert_57_28_3.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T57_28
      hfix57_28 hinj57_28 hcardT57_28
      (fun i => conj_mem_of_fixedPoints _ _ (T57_28 i) (hfix57_28 i) _)
      ⟨57, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T57_28_2 Q2.hfix57_28_2 Q2.hinj57_28_2
      Q2.hcardT57_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_28_2 i) (Q2.hfix57_28_2 i) _)
      colCert_57_28_4.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T57_28
      hfix57_28 hinj57_28 hcardT57_28
      (fun i => conj_mem_of_fixedPoints _ _ (T57_28 i) (hfix57_28 i) _)
      ⟨57, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T57_28_2 Q2.hfix57_28_2 Q2.hinj57_28_2
      Q2.hcardT57_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_28_2 i) (Q2.hfix57_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T57_28 = colFn colCertDiv_57_28_5.D1 (m := 5) from colCertDiv_57_28_5.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 5 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T57_28_2 = colFn colCertDiv_57_28_5.D2 (m := 5) from colCertDiv_57_28_5.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_28_5_match


theorem leaf_57_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T57_28
      hfix57_28 hinj57_28 hcardT57_28
      (fun i => conj_mem_of_fixedPoints _ _ (T57_28 i) (hfix57_28 i) _)
      ⟨57, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T57_28_2 Q2.hfix57_28_2 Q2.hinj57_28_2
      Q2.hcardT57_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_28_2 i) (Q2.hfix57_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T57_28 = colFn colCertDiv_57_28_10.D1 (m := 5) from colCertDiv_57_28_10.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 10 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T57_28_2 = colFn colCertDiv_57_28_10.D2 (m := 5) from colCertDiv_57_28_10.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_28_10_match


theorem leaf_57_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T57_28
      hfix57_28 hinj57_28 hcardT57_28
      (fun i => conj_mem_of_fixedPoints _ _ (T57_28 i) (hfix57_28 i) _)
      ⟨57, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T57_28_2 Q2.hfix57_28_2 Q2.hinj57_28_2
      Q2.hcardT57_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_28_2 i) (Q2.hfix57_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T57_28 = colFn colCertDiv_57_28_15.D1 (m := 5) from colCertDiv_57_28_15.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 15 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T57_28_2 = colFn colCertDiv_57_28_15.D2 (m := 5) from colCertDiv_57_28_15.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_28_15_match


theorem leaf_57_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T57_28
      hfix57_28 hinj57_28 hcardT57_28
      (fun i => conj_mem_of_fixedPoints _ _ (T57_28 i) (hfix57_28 i) _)
      ⟨57, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T57_28_2 Q2.hfix57_28_2 Q2.hinj57_28_2
      Q2.hcardT57_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_28_2 i) (Q2.hfix57_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T57_28 = colFn colCertDiv_57_28_20.D1 (m := 5) from colCertDiv_57_28_20.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 20 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T57_28_2 = colFn colCertDiv_57_28_20.D2 (m := 5) from colCertDiv_57_28_20.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_28_20_match


theorem leaf_57_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T57_33
      hfix57_33 hinj57_33 hcardT57_33
      (fun i => conj_mem_of_fixedPoints _ _ (T57_33 i) (hfix57_33 i) _)
      ⟨57, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T57_33_2 Q2.hfix57_33_2 Q2.hinj57_33_2
      Q2.hcardT57_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_33_2 i) (Q2.hfix57_33_2 i) _)
      colCert_57_33_0.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T57_33
      hfix57_33 hinj57_33 hcardT57_33
      (fun i => conj_mem_of_fixedPoints _ _ (T57_33 i) (hfix57_33 i) _)
      ⟨57, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T57_33_2 Q2.hfix57_33_2 Q2.hinj57_33_2
      Q2.hcardT57_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_33_2 i) (Q2.hfix57_33_2 i) _)
      colCert_57_33_1.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T57_33
      hfix57_33 hinj57_33 hcardT57_33
      (fun i => conj_mem_of_fixedPoints _ _ (T57_33 i) (hfix57_33 i) _)
      ⟨57, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T57_33_2 Q2.hfix57_33_2 Q2.hinj57_33_2
      Q2.hcardT57_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_33_2 i) (Q2.hfix57_33_2 i) _)
      colCert_57_33_2.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T57_33
      hfix57_33 hinj57_33 hcardT57_33
      (fun i => conj_mem_of_fixedPoints _ _ (T57_33 i) (hfix57_33 i) _)
      ⟨57, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T57_33_2 Q2.hfix57_33_2 Q2.hinj57_33_2
      Q2.hcardT57_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_33_2 i) (Q2.hfix57_33_2 i) _)
      colCert_57_33_3.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T57_33
      hfix57_33 hinj57_33 hcardT57_33
      (fun i => conj_mem_of_fixedPoints _ _ (T57_33 i) (hfix57_33 i) _)
      ⟨57, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T57_33_2 Q2.hfix57_33_2 Q2.hinj57_33_2
      Q2.hcardT57_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_33_2 i) (Q2.hfix57_33_2 i) _)
      colCert_57_33_4.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T57_33
      hfix57_33 hinj57_33 hcardT57_33
      (fun i => conj_mem_of_fixedPoints _ _ (T57_33 i) (hfix57_33 i) _)
      ⟨57, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T57_33_2 Q2.hfix57_33_2 Q2.hinj57_33_2
      Q2.hcardT57_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_33_2 i) (Q2.hfix57_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T57_33 = colFn colCertDiv_57_33_5.D1 (m := 5) from colCertDiv_57_33_5.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T57_33_2 = colFn colCertDiv_57_33_5.D2 (m := 5) from colCertDiv_57_33_5.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_33_5_match


theorem leaf_57_33_10 (hp : 10 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 10 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp)) T57_33
      hfix57_33 hinj57_33 hcardT57_33
      (fun i => conj_mem_of_fixedPoints _ _ (T57_33 i) (hfix57_33 i) _)
      ⟨57, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 10 hp) Q2.T57_33_2 Q2.hfix57_33_2 Q2.hinj57_33_2
      Q2.hcardT57_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_33_2 i) (Q2.hfix57_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 10 (transLenTr ⟨33, by decide⟩ 10 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T57_33 = colFn colCertDiv_57_33_10.D1 (m := 5) from colCertDiv_57_33_10.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 10 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T57_33_2 = colFn colCertDiv_57_33_10.D2 (m := 5) from colCertDiv_57_33_10.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_33_10_match


theorem leaf_57_33_15 (hp : 15 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 15 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp)) T57_33
      hfix57_33 hinj57_33 hcardT57_33
      (fun i => conj_mem_of_fixedPoints _ _ (T57_33 i) (hfix57_33 i) _)
      ⟨57, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 15 hp) Q2.T57_33_2 Q2.hfix57_33_2 Q2.hinj57_33_2
      Q2.hcardT57_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_33_2 i) (Q2.hfix57_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 15 (transLenTr ⟨33, by decide⟩ 15 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T57_33 = colFn colCertDiv_57_33_15.D1 (m := 5) from colCertDiv_57_33_15.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 15 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T57_33_2 = colFn colCertDiv_57_33_15.D2 (m := 5) from colCertDiv_57_33_15.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_33_15_match


theorem leaf_57_33_20 (hp : 20 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 20 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp)) T57_33
      hfix57_33 hinj57_33 hcardT57_33
      (fun i => conj_mem_of_fixedPoints _ _ (T57_33 i) (hfix57_33 i) _)
      ⟨57, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 20 hp) Q2.T57_33_2 Q2.hfix57_33_2 Q2.hinj57_33_2
      Q2.hcardT57_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_33_2 i) (Q2.hfix57_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 20 (transLenTr ⟨33, by decide⟩ 20 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T57_33 = colFn colCertDiv_57_33_20.D1 (m := 5) from colCertDiv_57_33_20.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 20 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T57_33_2 = colFn colCertDiv_57_33_20.D2 (m := 5) from colCertDiv_57_33_20.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_33_20_match


theorem leaf_57_38_0 (hp : 0 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 0 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 0 (transLenTr ⟨38, by decide⟩ 0 hp)) T57_38
      hfix57_38 hinj57_38 hcardT57_38
      (fun i => conj_mem_of_fixedPoints _ _ (T57_38 i) (hfix57_38 i) _)
      ⟨57, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 0 hp) Q2.T57_38_2 Q2.hfix57_38_2 Q2.hinj57_38_2
      Q2.hcardT57_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_38_2 i) (Q2.hfix57_38_2 i) _)
      colCert_57_38_0.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_38_1 (hp : 1 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 1 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 1 (transLenTr ⟨38, by decide⟩ 1 hp)) T57_38
      hfix57_38 hinj57_38 hcardT57_38
      (fun i => conj_mem_of_fixedPoints _ _ (T57_38 i) (hfix57_38 i) _)
      ⟨57, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 1 hp) Q2.T57_38_2 Q2.hfix57_38_2 Q2.hinj57_38_2
      Q2.hcardT57_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_38_2 i) (Q2.hfix57_38_2 i) _)
      colCert_57_38_1.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_38_2 (hp : 2 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 2 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 2 (transLenTr ⟨38, by decide⟩ 2 hp)) T57_38
      hfix57_38 hinj57_38 hcardT57_38
      (fun i => conj_mem_of_fixedPoints _ _ (T57_38 i) (hfix57_38 i) _)
      ⟨57, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 2 hp) Q2.T57_38_2 Q2.hfix57_38_2 Q2.hinj57_38_2
      Q2.hcardT57_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_38_2 i) (Q2.hfix57_38_2 i) _)
      colCert_57_38_2.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_38_3 (hp : 3 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 3 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 3 (transLenTr ⟨38, by decide⟩ 3 hp)) T57_38
      hfix57_38 hinj57_38 hcardT57_38
      (fun i => conj_mem_of_fixedPoints _ _ (T57_38 i) (hfix57_38 i) _)
      ⟨57, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 3 hp) Q2.T57_38_2 Q2.hfix57_38_2 Q2.hinj57_38_2
      Q2.hcardT57_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_38_2 i) (Q2.hfix57_38_2 i) _)
      colCert_57_38_3.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_38_4 (hp : 4 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 4 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 4 (transLenTr ⟨38, by decide⟩ 4 hp)) T57_38
      hfix57_38 hinj57_38 hcardT57_38
      (fun i => conj_mem_of_fixedPoints _ _ (T57_38 i) (hfix57_38 i) _)
      ⟨57, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 4 hp) Q2.T57_38_2 Q2.hfix57_38_2 Q2.hinj57_38_2
      Q2.hcardT57_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_38_2 i) (Q2.hfix57_38_2 i) _)
      colCert_57_38_4.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_38_5 (hp : 5 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 5 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp)) T57_38
      hfix57_38 hinj57_38 hcardT57_38
      (fun i => conj_mem_of_fixedPoints _ _ (T57_38 i) (hfix57_38 i) _)
      ⟨57, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 5 hp) Q2.T57_38_2 Q2.hfix57_38_2 Q2.hinj57_38_2
      Q2.hcardT57_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_38_2 i) (Q2.hfix57_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 5 (transLenTr ⟨38, by decide⟩ 5 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T57_38 = colFn colCertDiv_57_38_5.D1 (m := 5) from colCertDiv_57_38_5.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 5 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T57_38_2 = colFn colCertDiv_57_38_5.D2 (m := 5) from colCertDiv_57_38_5.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_38_5_match


theorem leaf_57_38_10 (hp : 10 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 10 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp)) T57_38
      hfix57_38 hinj57_38 hcardT57_38
      (fun i => conj_mem_of_fixedPoints _ _ (T57_38 i) (hfix57_38 i) _)
      ⟨57, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 10 hp) Q2.T57_38_2 Q2.hfix57_38_2 Q2.hinj57_38_2
      Q2.hcardT57_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_38_2 i) (Q2.hfix57_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 10 (transLenTr ⟨38, by decide⟩ 10 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T57_38 = colFn colCertDiv_57_38_10.D1 (m := 5) from colCertDiv_57_38_10.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 10 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T57_38_2 = colFn colCertDiv_57_38_10.D2 (m := 5) from colCertDiv_57_38_10.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_38_10_match


theorem leaf_57_38_15 (hp : 15 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 15 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp)) T57_38
      hfix57_38 hinj57_38 hcardT57_38
      (fun i => conj_mem_of_fixedPoints _ _ (T57_38 i) (hfix57_38 i) _)
      ⟨57, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 15 hp) Q2.T57_38_2 Q2.hfix57_38_2 Q2.hinj57_38_2
      Q2.hcardT57_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_38_2 i) (Q2.hfix57_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 15 (transLenTr ⟨38, by decide⟩ 15 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T57_38 = colFn colCertDiv_57_38_15.D1 (m := 5) from colCertDiv_57_38_15.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 15 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T57_38_2 = colFn colCertDiv_57_38_15.D2 (m := 5) from colCertDiv_57_38_15.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_38_15_match


theorem leaf_57_38_20 (hp : 20 < (Q2.transData.getD 38 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨38, by decide⟩ : Fin 148)) (colE2 ⟨38, by decide⟩ 20 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨38, by decide⟩ : Fin 148))
        (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨38, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp)) T57_38
      hfix57_38 hinj57_38 hcardT57_38
      (fun i => conj_mem_of_fixedPoints _ _ (T57_38 i) (hfix57_38 i) _)
      ⟨57, by decide⟩ ⟨38, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨38, by decide⟩ 20 hp) Q2.T57_38_2 Q2.hfix57_38_2 Q2.hinj57_38_2
      Q2.hcardT57_38_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_38_2 i) (Q2.hfix57_38_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨38, by decide⟩ 20 (transLenTr ⟨38, by decide⟩ 20 hp) : ↥(reps ⟨38, by decide⟩)) : Coordinate 1)
        T57_38 = colFn colCertDiv_57_38_20.D1 (m := 5) from colCertDiv_57_38_20.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨38, by decide⟩ 20 hp : ↥(Q2.reps ⟨38, by decide⟩)) : Coordinate 2)
        Q2.T57_38_2 = colFn colCertDiv_57_38_20.D2 (m := 5) from colCertDiv_57_38_20.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_38_20_match


theorem leaf_57_43_0 (hp : 0 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 0 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 0 (transLenTr ⟨43, by decide⟩ 0 hp)) T57_43
      hfix57_43 hinj57_43 hcardT57_43
      (fun i => conj_mem_of_fixedPoints _ _ (T57_43 i) (hfix57_43 i) _)
      ⟨57, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 0 hp) Q2.T57_43_2 Q2.hfix57_43_2 Q2.hinj57_43_2
      Q2.hcardT57_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_43_2 i) (Q2.hfix57_43_2 i) _)
      colCert_57_43_0.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_43_1 (hp : 1 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 1 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 1 (transLenTr ⟨43, by decide⟩ 1 hp)) T57_43
      hfix57_43 hinj57_43 hcardT57_43
      (fun i => conj_mem_of_fixedPoints _ _ (T57_43 i) (hfix57_43 i) _)
      ⟨57, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 1 hp) Q2.T57_43_2 Q2.hfix57_43_2 Q2.hinj57_43_2
      Q2.hcardT57_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_43_2 i) (Q2.hfix57_43_2 i) _)
      colCert_57_43_1.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_43_2 (hp : 2 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 2 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 2 (transLenTr ⟨43, by decide⟩ 2 hp)) T57_43
      hfix57_43 hinj57_43 hcardT57_43
      (fun i => conj_mem_of_fixedPoints _ _ (T57_43 i) (hfix57_43 i) _)
      ⟨57, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 2 hp) Q2.T57_43_2 Q2.hfix57_43_2 Q2.hinj57_43_2
      Q2.hcardT57_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_43_2 i) (Q2.hfix57_43_2 i) _)
      colCert_57_43_2.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_43_3 (hp : 3 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 3 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 3 (transLenTr ⟨43, by decide⟩ 3 hp)) T57_43
      hfix57_43 hinj57_43 hcardT57_43
      (fun i => conj_mem_of_fixedPoints _ _ (T57_43 i) (hfix57_43 i) _)
      ⟨57, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 3 hp) Q2.T57_43_2 Q2.hfix57_43_2 Q2.hinj57_43_2
      Q2.hcardT57_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_43_2 i) (Q2.hfix57_43_2 i) _)
      colCert_57_43_3.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_43_4 (hp : 4 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 4 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 4 (transLenTr ⟨43, by decide⟩ 4 hp)) T57_43
      hfix57_43 hinj57_43 hcardT57_43
      (fun i => conj_mem_of_fixedPoints _ _ (T57_43 i) (hfix57_43 i) _)
      ⟨57, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 4 hp) Q2.T57_43_2 Q2.hfix57_43_2 Q2.hinj57_43_2
      Q2.hcardT57_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_43_2 i) (Q2.hfix57_43_2 i) _)
      colCert_57_43_4.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_43_5 (hp : 5 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 5 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp)) T57_43
      hfix57_43 hinj57_43 hcardT57_43
      (fun i => conj_mem_of_fixedPoints _ _ (T57_43 i) (hfix57_43 i) _)
      ⟨57, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 5 hp) Q2.T57_43_2 Q2.hfix57_43_2 Q2.hinj57_43_2
      Q2.hcardT57_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_43_2 i) (Q2.hfix57_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 5 (transLenTr ⟨43, by decide⟩ 5 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T57_43 = colFn colCertDiv_57_43_5.D1 (m := 5) from colCertDiv_57_43_5.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 5 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T57_43_2 = colFn colCertDiv_57_43_5.D2 (m := 5) from colCertDiv_57_43_5.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_43_5_match


theorem leaf_57_43_10 (hp : 10 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 10 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp)) T57_43
      hfix57_43 hinj57_43 hcardT57_43
      (fun i => conj_mem_of_fixedPoints _ _ (T57_43 i) (hfix57_43 i) _)
      ⟨57, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 10 hp) Q2.T57_43_2 Q2.hfix57_43_2 Q2.hinj57_43_2
      Q2.hcardT57_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_43_2 i) (Q2.hfix57_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 10 (transLenTr ⟨43, by decide⟩ 10 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T57_43 = colFn colCertDiv_57_43_10.D1 (m := 5) from colCertDiv_57_43_10.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 10 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T57_43_2 = colFn colCertDiv_57_43_10.D2 (m := 5) from colCertDiv_57_43_10.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_43_10_match


theorem leaf_57_43_15 (hp : 15 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 15 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp)) T57_43
      hfix57_43 hinj57_43 hcardT57_43
      (fun i => conj_mem_of_fixedPoints _ _ (T57_43 i) (hfix57_43 i) _)
      ⟨57, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 15 hp) Q2.T57_43_2 Q2.hfix57_43_2 Q2.hinj57_43_2
      Q2.hcardT57_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_43_2 i) (Q2.hfix57_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 15 (transLenTr ⟨43, by decide⟩ 15 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T57_43 = colFn colCertDiv_57_43_15.D1 (m := 5) from colCertDiv_57_43_15.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 15 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T57_43_2 = colFn colCertDiv_57_43_15.D2 (m := 5) from colCertDiv_57_43_15.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_43_15_match


theorem leaf_57_43_20 (hp : 20 < (Q2.transData.getD 43 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨43, by decide⟩ : Fin 148)) (colE2 ⟨43, by decide⟩ 20 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨43, by decide⟩ : Fin 148))
        (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨43, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp)) T57_43
      hfix57_43 hinj57_43 hcardT57_43
      (fun i => conj_mem_of_fixedPoints _ _ (T57_43 i) (hfix57_43 i) _)
      ⟨57, by decide⟩ ⟨43, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨43, by decide⟩ 20 hp) Q2.T57_43_2 Q2.hfix57_43_2 Q2.hinj57_43_2
      Q2.hcardT57_43_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_43_2 i) (Q2.hfix57_43_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨43, by decide⟩ 20 (transLenTr ⟨43, by decide⟩ 20 hp) : ↥(reps ⟨43, by decide⟩)) : Coordinate 1)
        T57_43 = colFn colCertDiv_57_43_20.D1 (m := 5) from colCertDiv_57_43_20.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨43, by decide⟩ 20 hp : ↥(Q2.reps ⟨43, by decide⟩)) : Coordinate 2)
        Q2.T57_43_2 = colFn colCertDiv_57_43_20.D2 (m := 5) from colCertDiv_57_43_20.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_43_20_match


theorem leaf_57_48_0 (hp : 0 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 0 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 0 (transLenTr ⟨48, by decide⟩ 0 hp)) T57_48
      hfix57_48 hinj57_48 hcardT57_48
      (fun i => conj_mem_of_fixedPoints _ _ (T57_48 i) (hfix57_48 i) _)
      ⟨57, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 0 hp) Q2.T57_48_2 Q2.hfix57_48_2 Q2.hinj57_48_2
      Q2.hcardT57_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_48_2 i) (Q2.hfix57_48_2 i) _)
      colCert_57_48_0.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_48_1 (hp : 1 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 1 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 1 (transLenTr ⟨48, by decide⟩ 1 hp)) T57_48
      hfix57_48 hinj57_48 hcardT57_48
      (fun i => conj_mem_of_fixedPoints _ _ (T57_48 i) (hfix57_48 i) _)
      ⟨57, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 1 hp) Q2.T57_48_2 Q2.hfix57_48_2 Q2.hinj57_48_2
      Q2.hcardT57_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_48_2 i) (Q2.hfix57_48_2 i) _)
      colCert_57_48_1.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_48_2 (hp : 2 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 2 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 2 (transLenTr ⟨48, by decide⟩ 2 hp)) T57_48
      hfix57_48 hinj57_48 hcardT57_48
      (fun i => conj_mem_of_fixedPoints _ _ (T57_48 i) (hfix57_48 i) _)
      ⟨57, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 2 hp) Q2.T57_48_2 Q2.hfix57_48_2 Q2.hinj57_48_2
      Q2.hcardT57_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_48_2 i) (Q2.hfix57_48_2 i) _)
      colCert_57_48_2.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_48_3 (hp : 3 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 3 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 3 (transLenTr ⟨48, by decide⟩ 3 hp)) T57_48
      hfix57_48 hinj57_48 hcardT57_48
      (fun i => conj_mem_of_fixedPoints _ _ (T57_48 i) (hfix57_48 i) _)
      ⟨57, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 3 hp) Q2.T57_48_2 Q2.hfix57_48_2 Q2.hinj57_48_2
      Q2.hcardT57_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_48_2 i) (Q2.hfix57_48_2 i) _)
      colCert_57_48_3.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_48_4 (hp : 4 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 4 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 4 (transLenTr ⟨48, by decide⟩ 4 hp)) T57_48
      hfix57_48 hinj57_48 hcardT57_48
      (fun i => conj_mem_of_fixedPoints _ _ (T57_48 i) (hfix57_48 i) _)
      ⟨57, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 4 hp) Q2.T57_48_2 Q2.hfix57_48_2 Q2.hinj57_48_2
      Q2.hcardT57_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_48_2 i) (Q2.hfix57_48_2 i) _)
      colCert_57_48_4.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_48_5 (hp : 5 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 5 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp)) T57_48
      hfix57_48 hinj57_48 hcardT57_48
      (fun i => conj_mem_of_fixedPoints _ _ (T57_48 i) (hfix57_48 i) _)
      ⟨57, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 5 hp) Q2.T57_48_2 Q2.hfix57_48_2 Q2.hinj57_48_2
      Q2.hcardT57_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_48_2 i) (Q2.hfix57_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 5 (transLenTr ⟨48, by decide⟩ 5 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T57_48 = colFn colCertDiv_57_48_5.D1 (m := 5) from colCertDiv_57_48_5.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 5 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T57_48_2 = colFn colCertDiv_57_48_5.D2 (m := 5) from colCertDiv_57_48_5.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_48_5_match


theorem leaf_57_48_10 (hp : 10 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 10 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp)) T57_48
      hfix57_48 hinj57_48 hcardT57_48
      (fun i => conj_mem_of_fixedPoints _ _ (T57_48 i) (hfix57_48 i) _)
      ⟨57, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 10 hp) Q2.T57_48_2 Q2.hfix57_48_2 Q2.hinj57_48_2
      Q2.hcardT57_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_48_2 i) (Q2.hfix57_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 10 (transLenTr ⟨48, by decide⟩ 10 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T57_48 = colFn colCertDiv_57_48_10.D1 (m := 5) from colCertDiv_57_48_10.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 10 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T57_48_2 = colFn colCertDiv_57_48_10.D2 (m := 5) from colCertDiv_57_48_10.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_48_10_match


theorem leaf_57_48_15 (hp : 15 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 15 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp)) T57_48
      hfix57_48 hinj57_48 hcardT57_48
      (fun i => conj_mem_of_fixedPoints _ _ (T57_48 i) (hfix57_48 i) _)
      ⟨57, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 15 hp) Q2.T57_48_2 Q2.hfix57_48_2 Q2.hinj57_48_2
      Q2.hcardT57_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_48_2 i) (Q2.hfix57_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 15 (transLenTr ⟨48, by decide⟩ 15 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T57_48 = colFn colCertDiv_57_48_15.D1 (m := 5) from colCertDiv_57_48_15.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 15 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T57_48_2 = colFn colCertDiv_57_48_15.D2 (m := 5) from colCertDiv_57_48_15.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_48_15_match


theorem leaf_57_48_20 (hp : 20 < (Q2.transData.getD 48 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨48, by decide⟩ : Fin 148)) (colE2 ⟨48, by decide⟩ 20 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨48, by decide⟩ : Fin 148))
        (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨57, by decide⟩ : Fin 148) ⟨48, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp)) T57_48
      hfix57_48 hinj57_48 hcardT57_48
      (fun i => conj_mem_of_fixedPoints _ _ (T57_48 i) (hfix57_48 i) _)
      ⟨57, by decide⟩ ⟨48, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨48, by decide⟩ 20 hp) Q2.T57_48_2 Q2.hfix57_48_2 Q2.hinj57_48_2
      Q2.hcardT57_48_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_48_2 i) (Q2.hfix57_48_2 i) _)
      ?_).symm
  rw [show colData1 (⟨57, by decide⟩ : Fin 148)
        ((colE1 ⟨48, by decide⟩ 20 (transLenTr ⟨48, by decide⟩ 20 hp) : ↥(reps ⟨48, by decide⟩)) : Coordinate 1)
        T57_48 = colFn colCertDiv_57_48_20.D1 (m := 5) from colCertDiv_57_48_20.bind1,
    show colData2 (⟨57, by decide⟩ : Fin 148)
        ((colE2 ⟨48, by decide⟩ 20 hp : ↥(Q2.reps ⟨48, by decide⟩)) : Coordinate 2)
        Q2.T57_48_2 = colFn colCertDiv_57_48_20.D2 (m := 5) from colCertDiv_57_48_20.bind2]
  rw [alnId_57 j hj]
  exact fastcode_of_div ⟨57, by decide⟩ _ _ _
    ((alnId_57 j hj) ▸ Q2.listedAt (⟨57, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨57, by decide⟩ : Fin 148) hj hq).1) colCertDiv_57_48_20_match


theorem leaf_57_57_0 (hp : 0 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 0 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 0 (transLenTr ⟨57, by decide⟩ 0 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 0 (transLenTr ⟨57, by decide⟩ 0 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 0 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_0.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_1 (hp : 1 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 1 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 1 (transLenTr ⟨57, by decide⟩ 1 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 1 (transLenTr ⟨57, by decide⟩ 1 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 1 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_1.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_2 (hp : 2 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 2 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 2 (transLenTr ⟨57, by decide⟩ 2 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 2 (transLenTr ⟨57, by decide⟩ 2 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 2 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_2.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_3 (hp : 3 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 3 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 3 (transLenTr ⟨57, by decide⟩ 3 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 3 (transLenTr ⟨57, by decide⟩ 3 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 3 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_3.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_4 (hp : 4 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 4 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 4 (transLenTr ⟨57, by decide⟩ 4 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 4 (transLenTr ⟨57, by decide⟩ 4 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 4 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_4.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_5 (hp : 5 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 5 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 5 (transLenTr ⟨57, by decide⟩ 5 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 5 (transLenTr ⟨57, by decide⟩ 5 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 5 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_5.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_6 (hp : 6 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 6 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 6 (transLenTr ⟨57, by decide⟩ 6 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 6 (transLenTr ⟨57, by decide⟩ 6 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 6 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_6.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_7 (hp : 7 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 7 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 7 (transLenTr ⟨57, by decide⟩ 7 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 7 (transLenTr ⟨57, by decide⟩ 7 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 7 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_7.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_8 (hp : 8 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 8 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 8 (transLenTr ⟨57, by decide⟩ 8 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 8 (transLenTr ⟨57, by decide⟩ 8 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 8 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_8.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_9 (hp : 9 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 9 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 9 (transLenTr ⟨57, by decide⟩ 9 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 9 (transLenTr ⟨57, by decide⟩ 9 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 9 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_9.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_10 (hp : 10 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 10 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 10 (transLenTr ⟨57, by decide⟩ 10 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 10 (transLenTr ⟨57, by decide⟩ 10 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 10 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_10.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_11 (hp : 11 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 11 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 11 (transLenTr ⟨57, by decide⟩ 11 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 11 (transLenTr ⟨57, by decide⟩ 11 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 11 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_11.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_12 (hp : 12 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 12 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 12 (transLenTr ⟨57, by decide⟩ 12 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 12 (transLenTr ⟨57, by decide⟩ 12 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 12 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_12.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_13 (hp : 13 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 13 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 13 (transLenTr ⟨57, by decide⟩ 13 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 13 (transLenTr ⟨57, by decide⟩ 13 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 13 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_13.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_14 (hp : 14 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 14 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 14 (transLenTr ⟨57, by decide⟩ 14 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 14 (transLenTr ⟨57, by decide⟩ 14 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 14 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_14.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_15 (hp : 15 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 15 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 15 (transLenTr ⟨57, by decide⟩ 15 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 15 (transLenTr ⟨57, by decide⟩ 15 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 15 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_15.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_16 (hp : 16 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 16 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 16 (transLenTr ⟨57, by decide⟩ 16 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 16 (transLenTr ⟨57, by decide⟩ 16 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 16 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_16.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_17 (hp : 17 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 17 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 17 (transLenTr ⟨57, by decide⟩ 17 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 17 (transLenTr ⟨57, by decide⟩ 17 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 17 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_17.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_18 (hp : 18 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 18 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 18 (transLenTr ⟨57, by decide⟩ 18 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 18 (transLenTr ⟨57, by decide⟩ 18 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 18 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_18.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_19 (hp : 19 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 19 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 19 (transLenTr ⟨57, by decide⟩ 19 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 19 (transLenTr ⟨57, by decide⟩ 19 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 19 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_19.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_20 (hp : 20 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 20 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 20 (transLenTr ⟨57, by decide⟩ 20 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 20 (transLenTr ⟨57, by decide⟩ 20 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 20 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_20.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_21 (hp : 21 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 21 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 21 (transLenTr ⟨57, by decide⟩ 21 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 21 (transLenTr ⟨57, by decide⟩ 21 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 21 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_21.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_22 (hp : 22 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 22 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 22 (transLenTr ⟨57, by decide⟩ 22 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 22 (transLenTr ⟨57, by decide⟩ 22 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 22 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_22.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_23 (hp : 23 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 23 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 23 (transLenTr ⟨57, by decide⟩ 23 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 23 (transLenTr ⟨57, by decide⟩ 23 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 23 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_23.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_57_57_24 (hp : 24 < (Q2.transData.getD 57 []).length)
    (j : Nat) (hj : j < (repChars.getD 57 []).length)
    (hq : (normIsRep.getD 57 []).getD j false = true) :
    species (Q2.reps (⟨57, by decide⟩ : Fin 148)) (colE2 ⟨57, by decide⟩ 24 hp)
        (rowE2 (⟨57, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨57, by decide⟩ : Fin 148))
        (colE1 ⟨57, by decide⟩ 24 (transLenTr ⟨57, by decide⟩ 24 hp))
        (rowE1 (⟨57, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨57, by decide⟩ : Fin 148) ⟨57, by decide⟩ _
      (validAt ⟨57, by decide⟩ (listedAt ⟨57, by decide⟩ hj))
      (colE1 ⟨57, by decide⟩ 24 (transLenTr ⟨57, by decide⟩ 24 hp)) T57_57
      hfix57_57 hinj57_57 hcardT57_57
      (fun i => conj_mem_of_fixedPoints _ _ (T57_57 i) (hfix57_57 i) _)
      ⟨57, by decide⟩ ⟨57, by decide⟩ _
      (Q2.validAt ⟨57, by decide⟩ (Q2.listedAt ⟨57, by decide⟩
        (alnCheck_rep ⟨57, by decide⟩ hj hq).1))
      (colE2 ⟨57, by decide⟩ 24 hp) Q2.T57_57_2 Q2.hfix57_57_2 Q2.hinj57_57_2
      Q2.hcardT57_57_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T57_57_2 i) (Q2.hfix57_57_2 i) _)
      colCert_57_57_24.hD ?_).symm
  rw [alnId_57 j hj]


theorem leaf_58_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T58_6
      hfix58_6 hinj58_6 hcardT58_6
      (fun i => conj_mem_of_fixedPoints _ _ (T58_6 i) (hfix58_6 i) _)
      ⟨58, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T58_6_2 Q2.hfix58_6_2 Q2.hinj58_6_2
      Q2.hcardT58_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_6_2 i) (Q2.hfix58_6_2 i) _)
      colCert_58_6_0.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T58_6
      hfix58_6 hinj58_6 hcardT58_6
      (fun i => conj_mem_of_fixedPoints _ _ (T58_6 i) (hfix58_6 i) _)
      ⟨58, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T58_6_2 Q2.hfix58_6_2 Q2.hinj58_6_2
      Q2.hcardT58_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_6_2 i) (Q2.hfix58_6_2 i) _)
      colCert_58_6_1.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T58_6
      hfix58_6 hinj58_6 hcardT58_6
      (fun i => conj_mem_of_fixedPoints _ _ (T58_6 i) (hfix58_6 i) _)
      ⟨58, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T58_6_2 Q2.hfix58_6_2 Q2.hinj58_6_2
      Q2.hcardT58_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_6_2 i) (Q2.hfix58_6_2 i) _)
      colCert_58_6_2.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T58_6
      hfix58_6 hinj58_6 hcardT58_6
      (fun i => conj_mem_of_fixedPoints _ _ (T58_6 i) (hfix58_6 i) _)
      ⟨58, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T58_6_2 Q2.hfix58_6_2 Q2.hinj58_6_2
      Q2.hcardT58_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_6_2 i) (Q2.hfix58_6_2 i) _)
      colCert_58_6_3.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T58_6
      hfix58_6 hinj58_6 hcardT58_6
      (fun i => conj_mem_of_fixedPoints _ _ (T58_6 i) (hfix58_6 i) _)
      ⟨58, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T58_6_2 Q2.hfix58_6_2 Q2.hinj58_6_2
      Q2.hcardT58_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_6_2 i) (Q2.hfix58_6_2 i) _)
      colCert_58_6_4.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T58_12
      hfix58_12 hinj58_12 hcardT58_12
      (fun i => conj_mem_of_fixedPoints _ _ (T58_12 i) (hfix58_12 i) _)
      ⟨58, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T58_12_2 Q2.hfix58_12_2 Q2.hinj58_12_2
      Q2.hcardT58_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_12_2 i) (Q2.hfix58_12_2 i) _)
      colCert_58_12_0.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T58_12
      hfix58_12 hinj58_12 hcardT58_12
      (fun i => conj_mem_of_fixedPoints _ _ (T58_12 i) (hfix58_12 i) _)
      ⟨58, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T58_12_2 Q2.hfix58_12_2 Q2.hinj58_12_2
      Q2.hcardT58_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_12_2 i) (Q2.hfix58_12_2 i) _)
      colCert_58_12_1.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T58_12
      hfix58_12 hinj58_12 hcardT58_12
      (fun i => conj_mem_of_fixedPoints _ _ (T58_12 i) (hfix58_12 i) _)
      ⟨58, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T58_12_2 Q2.hfix58_12_2 Q2.hinj58_12_2
      Q2.hcardT58_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_12_2 i) (Q2.hfix58_12_2 i) _)
      colCert_58_12_2.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T58_12
      hfix58_12 hinj58_12 hcardT58_12
      (fun i => conj_mem_of_fixedPoints _ _ (T58_12 i) (hfix58_12 i) _)
      ⟨58, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T58_12_2 Q2.hfix58_12_2 Q2.hinj58_12_2
      Q2.hcardT58_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_12_2 i) (Q2.hfix58_12_2 i) _)
      colCert_58_12_3.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T58_12
      hfix58_12 hinj58_12 hcardT58_12
      (fun i => conj_mem_of_fixedPoints _ _ (T58_12 i) (hfix58_12 i) _)
      ⟨58, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T58_12_2 Q2.hfix58_12_2 Q2.hinj58_12_2
      Q2.hcardT58_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_12_2 i) (Q2.hfix58_12_2 i) _)
      colCert_58_12_4.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T58_24
      hfix58_24 hinj58_24 hcardT58_24
      (fun i => conj_mem_of_fixedPoints _ _ (T58_24 i) (hfix58_24 i) _)
      ⟨58, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T58_24_2 Q2.hfix58_24_2 Q2.hinj58_24_2
      Q2.hcardT58_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_24_2 i) (Q2.hfix58_24_2 i) _)
      colCert_58_24_0.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T58_24
      hfix58_24 hinj58_24 hcardT58_24
      (fun i => conj_mem_of_fixedPoints _ _ (T58_24 i) (hfix58_24 i) _)
      ⟨58, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T58_24_2 Q2.hfix58_24_2 Q2.hinj58_24_2
      Q2.hcardT58_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_24_2 i) (Q2.hfix58_24_2 i) _)
      colCert_58_24_1.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T58_24
      hfix58_24 hinj58_24 hcardT58_24
      (fun i => conj_mem_of_fixedPoints _ _ (T58_24 i) (hfix58_24 i) _)
      ⟨58, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T58_24_2 Q2.hfix58_24_2 Q2.hinj58_24_2
      Q2.hcardT58_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_24_2 i) (Q2.hfix58_24_2 i) _)
      colCert_58_24_2.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T58_24
      hfix58_24 hinj58_24 hcardT58_24
      (fun i => conj_mem_of_fixedPoints _ _ (T58_24 i) (hfix58_24 i) _)
      ⟨58, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T58_24_2 Q2.hfix58_24_2 Q2.hinj58_24_2
      Q2.hcardT58_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_24_2 i) (Q2.hfix58_24_2 i) _)
      colCert_58_24_3.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T58_24
      hfix58_24 hinj58_24 hcardT58_24
      (fun i => conj_mem_of_fixedPoints _ _ (T58_24 i) (hfix58_24 i) _)
      ⟨58, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T58_24_2 Q2.hfix58_24_2 Q2.hinj58_24_2
      Q2.hcardT58_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_24_2 i) (Q2.hfix58_24_2 i) _)
      colCert_58_24_4.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T58_24
      hfix58_24 hinj58_24 hcardT58_24
      (fun i => conj_mem_of_fixedPoints _ _ (T58_24 i) (hfix58_24 i) _)
      ⟨58, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T58_24_2 Q2.hfix58_24_2 Q2.hinj58_24_2
      Q2.hcardT58_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_24_2 i) (Q2.hfix58_24_2 i) _)
      colCert_58_24_5.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T58_24
      hfix58_24 hinj58_24 hcardT58_24
      (fun i => conj_mem_of_fixedPoints _ _ (T58_24 i) (hfix58_24 i) _)
      ⟨58, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T58_24_2 Q2.hfix58_24_2 Q2.hinj58_24_2
      Q2.hcardT58_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_24_2 i) (Q2.hfix58_24_2 i) _)
      colCert_58_24_10.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T58_24
      hfix58_24 hinj58_24 hcardT58_24
      (fun i => conj_mem_of_fixedPoints _ _ (T58_24 i) (hfix58_24 i) _)
      ⟨58, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T58_24_2 Q2.hfix58_24_2 Q2.hinj58_24_2
      Q2.hcardT58_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_24_2 i) (Q2.hfix58_24_2 i) _)
      colCert_58_24_15.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T58_24
      hfix58_24 hinj58_24 hcardT58_24
      (fun i => conj_mem_of_fixedPoints _ _ (T58_24 i) (hfix58_24 i) _)
      ⟨58, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T58_24_2 Q2.hfix58_24_2 Q2.hinj58_24_2
      Q2.hcardT58_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_24_2 i) (Q2.hfix58_24_2 i) _)
      colCert_58_24_20.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_28_0 (hp : 0 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 0 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 0 (transLenTr ⟨28, by decide⟩ 0 hp)) T58_28
      hfix58_28 hinj58_28 hcardT58_28
      (fun i => conj_mem_of_fixedPoints _ _ (T58_28 i) (hfix58_28 i) _)
      ⟨58, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 0 hp) Q2.T58_28_2 Q2.hfix58_28_2 Q2.hinj58_28_2
      Q2.hcardT58_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_28_2 i) (Q2.hfix58_28_2 i) _)
      colCert_58_28_0.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_28_1 (hp : 1 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 1 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 1 (transLenTr ⟨28, by decide⟩ 1 hp)) T58_28
      hfix58_28 hinj58_28 hcardT58_28
      (fun i => conj_mem_of_fixedPoints _ _ (T58_28 i) (hfix58_28 i) _)
      ⟨58, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 1 hp) Q2.T58_28_2 Q2.hfix58_28_2 Q2.hinj58_28_2
      Q2.hcardT58_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_28_2 i) (Q2.hfix58_28_2 i) _)
      colCert_58_28_1.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_28_2 (hp : 2 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 2 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 2 (transLenTr ⟨28, by decide⟩ 2 hp)) T58_28
      hfix58_28 hinj58_28 hcardT58_28
      (fun i => conj_mem_of_fixedPoints _ _ (T58_28 i) (hfix58_28 i) _)
      ⟨58, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 2 hp) Q2.T58_28_2 Q2.hfix58_28_2 Q2.hinj58_28_2
      Q2.hcardT58_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_28_2 i) (Q2.hfix58_28_2 i) _)
      colCert_58_28_2.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_28_3 (hp : 3 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 3 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 3 (transLenTr ⟨28, by decide⟩ 3 hp)) T58_28
      hfix58_28 hinj58_28 hcardT58_28
      (fun i => conj_mem_of_fixedPoints _ _ (T58_28 i) (hfix58_28 i) _)
      ⟨58, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 3 hp) Q2.T58_28_2 Q2.hfix58_28_2 Q2.hinj58_28_2
      Q2.hcardT58_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_28_2 i) (Q2.hfix58_28_2 i) _)
      colCert_58_28_3.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_28_4 (hp : 4 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 4 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 4 (transLenTr ⟨28, by decide⟩ 4 hp)) T58_28
      hfix58_28 hinj58_28 hcardT58_28
      (fun i => conj_mem_of_fixedPoints _ _ (T58_28 i) (hfix58_28 i) _)
      ⟨58, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 4 hp) Q2.T58_28_2 Q2.hfix58_28_2 Q2.hinj58_28_2
      Q2.hcardT58_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_28_2 i) (Q2.hfix58_28_2 i) _)
      colCert_58_28_4.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_28_5 (hp : 5 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 5 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp)) T58_28
      hfix58_28 hinj58_28 hcardT58_28
      (fun i => conj_mem_of_fixedPoints _ _ (T58_28 i) (hfix58_28 i) _)
      ⟨58, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 5 hp) Q2.T58_28_2 Q2.hfix58_28_2 Q2.hinj58_28_2
      Q2.hcardT58_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_28_2 i) (Q2.hfix58_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 5 (transLenTr ⟨28, by decide⟩ 5 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T58_28 = colFn colCertDiv_58_28_5.D1 (m := 5) from colCertDiv_58_28_5.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 5 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T58_28_2 = colFn colCertDiv_58_28_5.D2 (m := 5) from colCertDiv_58_28_5.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_28_5_match


theorem leaf_58_28_10 (hp : 10 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 10 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp)) T58_28
      hfix58_28 hinj58_28 hcardT58_28
      (fun i => conj_mem_of_fixedPoints _ _ (T58_28 i) (hfix58_28 i) _)
      ⟨58, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 10 hp) Q2.T58_28_2 Q2.hfix58_28_2 Q2.hinj58_28_2
      Q2.hcardT58_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_28_2 i) (Q2.hfix58_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 10 (transLenTr ⟨28, by decide⟩ 10 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T58_28 = colFn colCertDiv_58_28_10.D1 (m := 5) from colCertDiv_58_28_10.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 10 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T58_28_2 = colFn colCertDiv_58_28_10.D2 (m := 5) from colCertDiv_58_28_10.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_28_10_match


theorem leaf_58_28_15 (hp : 15 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 15 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp)) T58_28
      hfix58_28 hinj58_28 hcardT58_28
      (fun i => conj_mem_of_fixedPoints _ _ (T58_28 i) (hfix58_28 i) _)
      ⟨58, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 15 hp) Q2.T58_28_2 Q2.hfix58_28_2 Q2.hinj58_28_2
      Q2.hcardT58_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_28_2 i) (Q2.hfix58_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 15 (transLenTr ⟨28, by decide⟩ 15 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T58_28 = colFn colCertDiv_58_28_15.D1 (m := 5) from colCertDiv_58_28_15.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 15 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T58_28_2 = colFn colCertDiv_58_28_15.D2 (m := 5) from colCertDiv_58_28_15.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_28_15_match


theorem leaf_58_28_20 (hp : 20 < (Q2.transData.getD 28 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨28, by decide⟩ : Fin 148)) (colE2 ⟨28, by decide⟩ 20 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨28, by decide⟩ : Fin 148))
        (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨28, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp)) T58_28
      hfix58_28 hinj58_28 hcardT58_28
      (fun i => conj_mem_of_fixedPoints _ _ (T58_28 i) (hfix58_28 i) _)
      ⟨58, by decide⟩ ⟨28, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨28, by decide⟩ 20 hp) Q2.T58_28_2 Q2.hfix58_28_2 Q2.hinj58_28_2
      Q2.hcardT58_28_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_28_2 i) (Q2.hfix58_28_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨28, by decide⟩ 20 (transLenTr ⟨28, by decide⟩ 20 hp) : ↥(reps ⟨28, by decide⟩)) : Coordinate 1)
        T58_28 = colFn colCertDiv_58_28_20.D1 (m := 5) from colCertDiv_58_28_20.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨28, by decide⟩ 20 hp : ↥(Q2.reps ⟨28, by decide⟩)) : Coordinate 2)
        Q2.T58_28_2 = colFn colCertDiv_58_28_20.D2 (m := 5) from colCertDiv_58_28_20.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_28_20_match


theorem leaf_58_33_0 (hp : 0 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 0 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 0 (transLenTr ⟨33, by decide⟩ 0 hp)) T58_33
      hfix58_33 hinj58_33 hcardT58_33
      (fun i => conj_mem_of_fixedPoints _ _ (T58_33 i) (hfix58_33 i) _)
      ⟨58, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 0 hp) Q2.T58_33_2 Q2.hfix58_33_2 Q2.hinj58_33_2
      Q2.hcardT58_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_33_2 i) (Q2.hfix58_33_2 i) _)
      colCert_58_33_0.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_33_1 (hp : 1 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 1 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 1 (transLenTr ⟨33, by decide⟩ 1 hp)) T58_33
      hfix58_33 hinj58_33 hcardT58_33
      (fun i => conj_mem_of_fixedPoints _ _ (T58_33 i) (hfix58_33 i) _)
      ⟨58, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 1 hp) Q2.T58_33_2 Q2.hfix58_33_2 Q2.hinj58_33_2
      Q2.hcardT58_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_33_2 i) (Q2.hfix58_33_2 i) _)
      colCert_58_33_1.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_33_2 (hp : 2 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 2 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 2 (transLenTr ⟨33, by decide⟩ 2 hp)) T58_33
      hfix58_33 hinj58_33 hcardT58_33
      (fun i => conj_mem_of_fixedPoints _ _ (T58_33 i) (hfix58_33 i) _)
      ⟨58, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 2 hp) Q2.T58_33_2 Q2.hfix58_33_2 Q2.hinj58_33_2
      Q2.hcardT58_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_33_2 i) (Q2.hfix58_33_2 i) _)
      colCert_58_33_2.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_33_3 (hp : 3 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 3 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 3 (transLenTr ⟨33, by decide⟩ 3 hp)) T58_33
      hfix58_33 hinj58_33 hcardT58_33
      (fun i => conj_mem_of_fixedPoints _ _ (T58_33 i) (hfix58_33 i) _)
      ⟨58, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 3 hp) Q2.T58_33_2 Q2.hfix58_33_2 Q2.hinj58_33_2
      Q2.hcardT58_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_33_2 i) (Q2.hfix58_33_2 i) _)
      colCert_58_33_3.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_33_4 (hp : 4 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 4 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨58, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 4 (transLenTr ⟨33, by decide⟩ 4 hp)) T58_33
      hfix58_33 hinj58_33 hcardT58_33
      (fun i => conj_mem_of_fixedPoints _ _ (T58_33 i) (hfix58_33 i) _)
      ⟨58, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 4 hp) Q2.T58_33_2 Q2.hfix58_33_2 Q2.hinj58_33_2
      Q2.hcardT58_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_33_2 i) (Q2.hfix58_33_2 i) _)
      colCert_58_33_4.hD ?_).symm
  rw [alnId_58 j hj]


theorem leaf_58_33_5 (hp : 5 < (Q2.transData.getD 33 []).length)
    (j : Nat) (hj : j < (repChars.getD 58 []).length)
    (hq : (normIsRep.getD 58 []).getD j false = true) :
    species (Q2.reps (⟨33, by decide⟩ : Fin 148)) (colE2 ⟨33, by decide⟩ 5 hp)
        (rowE2 (⟨58, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨33, by decide⟩ : Fin 148))
        (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp))
        (rowE1 (⟨58, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨58, by decide⟩ : Fin 148) ⟨33, by decide⟩ _
      (validAt ⟨58, by decide⟩ (listedAt ⟨58, by decide⟩ hj))
      (colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp)) T58_33
      hfix58_33 hinj58_33 hcardT58_33
      (fun i => conj_mem_of_fixedPoints _ _ (T58_33 i) (hfix58_33 i) _)
      ⟨58, by decide⟩ ⟨33, by decide⟩ _
      (Q2.validAt ⟨58, by decide⟩ (Q2.listedAt ⟨58, by decide⟩
        (alnCheck_rep ⟨58, by decide⟩ hj hq).1))
      (colE2 ⟨33, by decide⟩ 5 hp) Q2.T58_33_2 Q2.hfix58_33_2 Q2.hinj58_33_2
      Q2.hcardT58_33_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T58_33_2 i) (Q2.hfix58_33_2 i) _)
      ?_).symm
  rw [show colData1 (⟨58, by decide⟩ : Fin 148)
        ((colE1 ⟨33, by decide⟩ 5 (transLenTr ⟨33, by decide⟩ 5 hp) : ↥(reps ⟨33, by decide⟩)) : Coordinate 1)
        T58_33 = colFn colCertDiv_58_33_5.D1 (m := 5) from colCertDiv_58_33_5.bind1,
    show colData2 (⟨58, by decide⟩ : Fin 148)
        ((colE2 ⟨33, by decide⟩ 5 hp : ↥(Q2.reps ⟨33, by decide⟩)) : Coordinate 2)
        Q2.T58_33_2 = colFn colCertDiv_58_33_5.D2 (m := 5) from colCertDiv_58_33_5.bind2]
  rw [alnId_58 j hj]
  exact fastcode_of_div ⟨58, by decide⟩ _ _ _
    ((alnId_58 j hj) ▸ Q2.listedAt (⟨58, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨58, by decide⟩ : Fin 148) hj hq).1) colCertDiv_58_33_5_match


end LeanDring.P5Presentation
