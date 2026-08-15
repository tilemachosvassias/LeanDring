/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.ColCdd.C038
import LeanDring.P5.Data.ColCdd.C039
import LeanDring.P5.Data.ColRestCheap.C155
import LeanDring.P5.Data.ColRestCheap.C156
import LeanDring.P5.Data.ColRestCheap.C157
import LeanDring.P5.Data.ColRestCheap.C158
import LeanDring.P5.Data.ColRestCheap.C159
import LeanDring.P5.Data.ColTau.C003
import LeanDring.P5.Data.EntryK.C016
import LeanDring.P5.Certificate.RingIsomorphism.MatchCore
import LeanDring.P5.Data.SpeciesAlign.C014
import LeanDring.P5.Data.SpeciesAlign.C015
import LeanDring.P5.Data.SpeciesAlign.C016
import LeanDring.P5.Data.SpeciesAlign.C017
import LeanDring.P5.Certificate.SpeciesTable.Twin2.SpeciesTau.Chunk01

/-! # Stage-5 leaves, chunk 8 (auto-emitted).  -/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem leaf_66_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T66_45
      hfix66_45 hinj66_45 hcardT66_45
      (fun i => conj_mem_of_fixedPoints _ _ (T66_45 i) (hfix66_45 i) _)
      ⟨66, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T66_45_2 Q2.hfix66_45_2 Q2.hinj66_45_2
      Q2.hcardT66_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_45_2 i) (Q2.hfix66_45_2 i) _)
      colCert_66_45_10.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T66_45
      hfix66_45 hinj66_45 hcardT66_45
      (fun i => conj_mem_of_fixedPoints _ _ (T66_45 i) (hfix66_45 i) _)
      ⟨66, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T66_45_2 Q2.hfix66_45_2 Q2.hinj66_45_2
      Q2.hcardT66_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_45_2 i) (Q2.hfix66_45_2 i) _)
      colCert_66_45_15.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T66_45
      hfix66_45 hinj66_45 hcardT66_45
      (fun i => conj_mem_of_fixedPoints _ _ (T66_45 i) (hfix66_45 i) _)
      ⟨66, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T66_45_2 Q2.hfix66_45_2 Q2.hinj66_45_2
      Q2.hcardT66_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_45_2 i) (Q2.hfix66_45_2 i) _)
      colCert_66_45_20.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T66_50
      hfix66_50 hinj66_50 hcardT66_50
      (fun i => conj_mem_of_fixedPoints _ _ (T66_50 i) (hfix66_50 i) _)
      ⟨66, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T66_50_2 Q2.hfix66_50_2 Q2.hinj66_50_2
      Q2.hcardT66_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_50_2 i) (Q2.hfix66_50_2 i) _)
      colCert_66_50_0.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T66_50
      hfix66_50 hinj66_50 hcardT66_50
      (fun i => conj_mem_of_fixedPoints _ _ (T66_50 i) (hfix66_50 i) _)
      ⟨66, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T66_50_2 Q2.hfix66_50_2 Q2.hinj66_50_2
      Q2.hcardT66_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_50_2 i) (Q2.hfix66_50_2 i) _)
      colCert_66_50_1.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T66_50
      hfix66_50 hinj66_50 hcardT66_50
      (fun i => conj_mem_of_fixedPoints _ _ (T66_50 i) (hfix66_50 i) _)
      ⟨66, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T66_50_2 Q2.hfix66_50_2 Q2.hinj66_50_2
      Q2.hcardT66_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_50_2 i) (Q2.hfix66_50_2 i) _)
      colCert_66_50_2.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T66_50
      hfix66_50 hinj66_50 hcardT66_50
      (fun i => conj_mem_of_fixedPoints _ _ (T66_50 i) (hfix66_50 i) _)
      ⟨66, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T66_50_2 Q2.hfix66_50_2 Q2.hinj66_50_2
      Q2.hcardT66_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_50_2 i) (Q2.hfix66_50_2 i) _)
      colCert_66_50_3.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T66_50
      hfix66_50 hinj66_50 hcardT66_50
      (fun i => conj_mem_of_fixedPoints _ _ (T66_50 i) (hfix66_50 i) _)
      ⟨66, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T66_50_2 Q2.hfix66_50_2 Q2.hinj66_50_2
      Q2.hcardT66_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_50_2 i) (Q2.hfix66_50_2 i) _)
      colCert_66_50_4.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T66_50
      hfix66_50 hinj66_50 hcardT66_50
      (fun i => conj_mem_of_fixedPoints _ _ (T66_50 i) (hfix66_50 i) _)
      ⟨66, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T66_50_2 Q2.hfix66_50_2 Q2.hinj66_50_2
      Q2.hcardT66_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_50_2 i) (Q2.hfix66_50_2 i) _)
      colCert_66_50_5.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T66_50
      hfix66_50 hinj66_50 hcardT66_50
      (fun i => conj_mem_of_fixedPoints _ _ (T66_50 i) (hfix66_50 i) _)
      ⟨66, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T66_50_2 Q2.hfix66_50_2 Q2.hinj66_50_2
      Q2.hcardT66_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_50_2 i) (Q2.hfix66_50_2 i) _)
      colCert_66_50_10.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T66_50
      hfix66_50 hinj66_50 hcardT66_50
      (fun i => conj_mem_of_fixedPoints _ _ (T66_50 i) (hfix66_50 i) _)
      ⟨66, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T66_50_2 Q2.hfix66_50_2 Q2.hinj66_50_2
      Q2.hcardT66_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_50_2 i) (Q2.hfix66_50_2 i) _)
      colCert_66_50_15.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T66_50
      hfix66_50 hinj66_50 hcardT66_50
      (fun i => conj_mem_of_fixedPoints _ _ (T66_50 i) (hfix66_50 i) _)
      ⟨66, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T66_50_2 Q2.hfix66_50_2 Q2.hinj66_50_2
      Q2.hcardT66_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_50_2 i) (Q2.hfix66_50_2 i) _)
      colCert_66_50_20.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_0 (hp : 0 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 0 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 0 (transLenTr ⟨66, by decide⟩ 0 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 0 (transLenTr ⟨66, by decide⟩ 0 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 0 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_0.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_1 (hp : 1 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 1 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 1 (transLenTr ⟨66, by decide⟩ 1 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 1 (transLenTr ⟨66, by decide⟩ 1 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 1 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_1.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_2 (hp : 2 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 2 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 2 (transLenTr ⟨66, by decide⟩ 2 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 2 (transLenTr ⟨66, by decide⟩ 2 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 2 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_2.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_3 (hp : 3 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 3 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 3 (transLenTr ⟨66, by decide⟩ 3 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 3 (transLenTr ⟨66, by decide⟩ 3 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 3 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_3.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_4 (hp : 4 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 4 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 4 (transLenTr ⟨66, by decide⟩ 4 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 4 (transLenTr ⟨66, by decide⟩ 4 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 4 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_4.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_5 (hp : 5 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 5 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 5 (transLenTr ⟨66, by decide⟩ 5 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 5 (transLenTr ⟨66, by decide⟩ 5 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 5 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_5.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_6 (hp : 6 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 6 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 6 (transLenTr ⟨66, by decide⟩ 6 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 6 (transLenTr ⟨66, by decide⟩ 6 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 6 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_6.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_7 (hp : 7 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 7 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 7 (transLenTr ⟨66, by decide⟩ 7 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 7 (transLenTr ⟨66, by decide⟩ 7 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 7 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_7.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_8 (hp : 8 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 8 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 8 (transLenTr ⟨66, by decide⟩ 8 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 8 (transLenTr ⟨66, by decide⟩ 8 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 8 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_8.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_9 (hp : 9 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 9 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 9 (transLenTr ⟨66, by decide⟩ 9 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 9 (transLenTr ⟨66, by decide⟩ 9 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 9 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_9.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_10 (hp : 10 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 10 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 10 (transLenTr ⟨66, by decide⟩ 10 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 10 (transLenTr ⟨66, by decide⟩ 10 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 10 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_10.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_11 (hp : 11 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 11 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 11 (transLenTr ⟨66, by decide⟩ 11 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 11 (transLenTr ⟨66, by decide⟩ 11 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 11 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_11.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_12 (hp : 12 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 12 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 12 (transLenTr ⟨66, by decide⟩ 12 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 12 (transLenTr ⟨66, by decide⟩ 12 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 12 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_12.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_13 (hp : 13 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 13 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 13 (transLenTr ⟨66, by decide⟩ 13 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 13 (transLenTr ⟨66, by decide⟩ 13 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 13 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_13.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_14 (hp : 14 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 14 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 14 (transLenTr ⟨66, by decide⟩ 14 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 14 (transLenTr ⟨66, by decide⟩ 14 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 14 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_14.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_15 (hp : 15 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 15 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 15 (transLenTr ⟨66, by decide⟩ 15 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 15 (transLenTr ⟨66, by decide⟩ 15 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 15 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_15.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_16 (hp : 16 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 16 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 16 (transLenTr ⟨66, by decide⟩ 16 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 16 (transLenTr ⟨66, by decide⟩ 16 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 16 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_16.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_17 (hp : 17 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 17 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 17 (transLenTr ⟨66, by decide⟩ 17 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 17 (transLenTr ⟨66, by decide⟩ 17 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 17 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_17.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_18 (hp : 18 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 18 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 18 (transLenTr ⟨66, by decide⟩ 18 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 18 (transLenTr ⟨66, by decide⟩ 18 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 18 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_18.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_19 (hp : 19 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 19 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 19 (transLenTr ⟨66, by decide⟩ 19 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 19 (transLenTr ⟨66, by decide⟩ 19 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 19 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_19.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_20 (hp : 20 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 20 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 20 (transLenTr ⟨66, by decide⟩ 20 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 20 (transLenTr ⟨66, by decide⟩ 20 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 20 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_20.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_21 (hp : 21 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 21 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 21 (transLenTr ⟨66, by decide⟩ 21 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 21 (transLenTr ⟨66, by decide⟩ 21 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 21 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_21.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_22 (hp : 22 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 22 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 22 (transLenTr ⟨66, by decide⟩ 22 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 22 (transLenTr ⟨66, by decide⟩ 22 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 22 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_22.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_23 (hp : 23 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 23 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 23 (transLenTr ⟨66, by decide⟩ 23 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 23 (transLenTr ⟨66, by decide⟩ 23 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 23 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_23.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_66_66_24 (hp : 24 < (Q2.transData.getD 66 []).length)
    (j : Nat) (hj : j < (repChars.getD 66 []).length)
    (hq : (normIsRep.getD 66 []).getD j false = true) :
    species (Q2.reps (⟨66, by decide⟩ : Fin 148)) (colE2 ⟨66, by decide⟩ 24 hp)
        (rowE2 (⟨66, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨66, by decide⟩ : Fin 148))
        (colE1 ⟨66, by decide⟩ 24 (transLenTr ⟨66, by decide⟩ 24 hp))
        (rowE1 (⟨66, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨66, by decide⟩ : Fin 148) ⟨66, by decide⟩ _
      (validAt ⟨66, by decide⟩ (listedAt ⟨66, by decide⟩ hj))
      (colE1 ⟨66, by decide⟩ 24 (transLenTr ⟨66, by decide⟩ 24 hp)) T66_66
      hfix66_66 hinj66_66 hcardT66_66
      (fun i => conj_mem_of_fixedPoints _ _ (T66_66 i) (hfix66_66 i) _)
      ⟨66, by decide⟩ ⟨66, by decide⟩ _
      (Q2.validAt ⟨66, by decide⟩ (Q2.listedAt ⟨66, by decide⟩
        (alnCheck_rep ⟨66, by decide⟩ hj hq).1))
      (colE2 ⟨66, by decide⟩ 24 hp) Q2.T66_66_2 Q2.hfix66_66_2 Q2.hinj66_66_2
      Q2.hcardT66_66_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T66_66_2 i) (Q2.hfix66_66_2 i) _)
      colCert_66_66_24.hD ?_).symm
  rw [alnId_66 j hj]


theorem leaf_67_7_0 (hp : 0 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 0 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp)) T67_7
      hfix67_7 hinj67_7 hcardT67_7
      (fun i => conj_mem_of_fixedPoints _ _ (T67_7 i) (hfix67_7 i) _)
      ⟨67, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 0 hp) Q2.T67_7_2 Q2.hfix67_7_2 Q2.hinj67_7_2
      Q2.hcardT67_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_7_2 i) (Q2.hfix67_7_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨7, by decide⟩ 0 (transLenTr ⟨7, by decide⟩ 0 hp) : ↥(reps ⟨7, by decide⟩)) : Coordinate 1)
        T67_7 = colFn colCert_67_7_0.D (m := 25) from colCert_67_7_0.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨7, by decide⟩ 0 hp : ↥(Q2.reps ⟨7, by decide⟩)) : Coordinate 2)
        Q2.T67_7_2 = colFn colCert_67_7_0.D (m := 25) from colCert_67_7_0.bind2]
  exact alnAll_67_7_0 j hj hq

theorem leaf_67_7_1 (hp : 1 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 1 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp)) T67_7
      hfix67_7 hinj67_7 hcardT67_7
      (fun i => conj_mem_of_fixedPoints _ _ (T67_7 i) (hfix67_7 i) _)
      ⟨67, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 1 hp) Q2.T67_7_2 Q2.hfix67_7_2 Q2.hinj67_7_2
      Q2.hcardT67_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_7_2 i) (Q2.hfix67_7_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨7, by decide⟩ 1 (transLenTr ⟨7, by decide⟩ 1 hp) : ↥(reps ⟨7, by decide⟩)) : Coordinate 1)
        T67_7 = colFn colCert_67_7_1.D (m := 25) from colCert_67_7_1.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨7, by decide⟩ 1 hp : ↥(Q2.reps ⟨7, by decide⟩)) : Coordinate 2)
        Q2.T67_7_2 = colFn colCert_67_7_1.D (m := 25) from colCert_67_7_1.bind2]
  exact alnAll_67_7_1 j hj hq

theorem leaf_67_7_2 (hp : 2 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 2 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp)) T67_7
      hfix67_7 hinj67_7 hcardT67_7
      (fun i => conj_mem_of_fixedPoints _ _ (T67_7 i) (hfix67_7 i) _)
      ⟨67, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 2 hp) Q2.T67_7_2 Q2.hfix67_7_2 Q2.hinj67_7_2
      Q2.hcardT67_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_7_2 i) (Q2.hfix67_7_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨7, by decide⟩ 2 (transLenTr ⟨7, by decide⟩ 2 hp) : ↥(reps ⟨7, by decide⟩)) : Coordinate 1)
        T67_7 = colFn colCert_67_7_2.D (m := 25) from colCert_67_7_2.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨7, by decide⟩ 2 hp : ↥(Q2.reps ⟨7, by decide⟩)) : Coordinate 2)
        Q2.T67_7_2 = colFn colCert_67_7_2.D (m := 25) from colCert_67_7_2.bind2]
  exact alnAll_67_7_2 j hj hq

theorem leaf_67_7_3 (hp : 3 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 3 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp)) T67_7
      hfix67_7 hinj67_7 hcardT67_7
      (fun i => conj_mem_of_fixedPoints _ _ (T67_7 i) (hfix67_7 i) _)
      ⟨67, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 3 hp) Q2.T67_7_2 Q2.hfix67_7_2 Q2.hinj67_7_2
      Q2.hcardT67_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_7_2 i) (Q2.hfix67_7_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨7, by decide⟩ 3 (transLenTr ⟨7, by decide⟩ 3 hp) : ↥(reps ⟨7, by decide⟩)) : Coordinate 1)
        T67_7 = colFn colCert_67_7_3.D (m := 25) from colCert_67_7_3.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨7, by decide⟩ 3 hp : ↥(Q2.reps ⟨7, by decide⟩)) : Coordinate 2)
        Q2.T67_7_2 = colFn colCert_67_7_3.D (m := 25) from colCert_67_7_3.bind2]
  exact alnAll_67_7_3 j hj hq

theorem leaf_67_7_4 (hp : 4 < (Q2.transData.getD 7 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨7, by decide⟩ : Fin 148)) (colE2 ⟨7, by decide⟩ 4 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨7, by decide⟩ : Fin 148))
        (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨7, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp)) T67_7
      hfix67_7 hinj67_7 hcardT67_7
      (fun i => conj_mem_of_fixedPoints _ _ (T67_7 i) (hfix67_7 i) _)
      ⟨67, by decide⟩ ⟨7, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨7, by decide⟩ 4 hp) Q2.T67_7_2 Q2.hfix67_7_2 Q2.hinj67_7_2
      Q2.hcardT67_7_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_7_2 i) (Q2.hfix67_7_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨7, by decide⟩ 4 (transLenTr ⟨7, by decide⟩ 4 hp) : ↥(reps ⟨7, by decide⟩)) : Coordinate 1)
        T67_7 = colFn colCert_67_7_4.D (m := 25) from colCert_67_7_4.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨7, by decide⟩ 4 hp : ↥(Q2.reps ⟨7, by decide⟩)) : Coordinate 2)
        Q2.T67_7_2 = colFn colCert_67_7_4.D (m := 25) from colCert_67_7_4.bind2]
  exact alnAll_67_7_4 j hj hq

theorem leaf_67_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T67_12
      hfix67_12 hinj67_12 hcardT67_12
      (fun i => conj_mem_of_fixedPoints _ _ (T67_12 i) (hfix67_12 i) _)
      ⟨67, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T67_12_2 Q2.hfix67_12_2 Q2.hinj67_12_2
      Q2.hcardT67_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_12_2 i) (Q2.hfix67_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T67_12 = colFn colCert_67_12_0.D (m := 25) from colCert_67_12_0.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 0 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T67_12_2 = colFn colCert_67_12_0.D (m := 25) from colCert_67_12_0.bind2]
  exact alnAll_67_12_0 j hj hq

theorem leaf_67_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T67_12
      hfix67_12 hinj67_12 hcardT67_12
      (fun i => conj_mem_of_fixedPoints _ _ (T67_12 i) (hfix67_12 i) _)
      ⟨67, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T67_12_2 Q2.hfix67_12_2 Q2.hinj67_12_2
      Q2.hcardT67_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_12_2 i) (Q2.hfix67_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T67_12 = colFn colCert_67_12_1.D (m := 25) from colCert_67_12_1.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 1 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T67_12_2 = colFn colCert_67_12_1.D (m := 25) from colCert_67_12_1.bind2]
  exact alnAll_67_12_1 j hj hq

theorem leaf_67_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T67_12
      hfix67_12 hinj67_12 hcardT67_12
      (fun i => conj_mem_of_fixedPoints _ _ (T67_12 i) (hfix67_12 i) _)
      ⟨67, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T67_12_2 Q2.hfix67_12_2 Q2.hinj67_12_2
      Q2.hcardT67_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_12_2 i) (Q2.hfix67_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T67_12 = colFn colCert_67_12_2.D (m := 25) from colCert_67_12_2.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 2 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T67_12_2 = colFn colCert_67_12_2.D (m := 25) from colCert_67_12_2.bind2]
  exact alnAll_67_12_2 j hj hq

theorem leaf_67_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T67_12
      hfix67_12 hinj67_12 hcardT67_12
      (fun i => conj_mem_of_fixedPoints _ _ (T67_12 i) (hfix67_12 i) _)
      ⟨67, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T67_12_2 Q2.hfix67_12_2 Q2.hinj67_12_2
      Q2.hcardT67_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_12_2 i) (Q2.hfix67_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T67_12 = colFn colCert_67_12_3.D (m := 25) from colCert_67_12_3.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 3 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T67_12_2 = colFn colCert_67_12_3.D (m := 25) from colCert_67_12_3.bind2]
  exact alnAll_67_12_3 j hj hq

theorem leaf_67_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T67_12
      hfix67_12 hinj67_12 hcardT67_12
      (fun i => conj_mem_of_fixedPoints _ _ (T67_12 i) (hfix67_12 i) _)
      ⟨67, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T67_12_2 Q2.hfix67_12_2 Q2.hinj67_12_2
      Q2.hcardT67_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_12_2 i) (Q2.hfix67_12_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp) : ↥(reps ⟨12, by decide⟩)) : Coordinate 1)
        T67_12 = colFn colCert_67_12_4.D (m := 25) from colCert_67_12_4.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨12, by decide⟩ 4 hp : ↥(Q2.reps ⟨12, by decide⟩)) : Coordinate 2)
        Q2.T67_12_2 = colFn colCert_67_12_4.D (m := 25) from colCert_67_12_4.bind2]
  exact alnAll_67_12_4 j hj hq

theorem leaf_67_25_0 (hp : 0 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 0 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp)) T67_25
      hfix67_25 hinj67_25 hcardT67_25
      (fun i => conj_mem_of_fixedPoints _ _ (T67_25 i) (hfix67_25 i) _)
      ⟨67, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 0 hp) Q2.T67_25_2 Q2.hfix67_25_2 Q2.hinj67_25_2
      Q2.hcardT67_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_25_2 i) (Q2.hfix67_25_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨25, by decide⟩ 0 (transLenTr ⟨25, by decide⟩ 0 hp) : ↥(reps ⟨25, by decide⟩)) : Coordinate 1)
        T67_25 = colFn colCert_67_25_0.D (m := 25) from colCert_67_25_0.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨25, by decide⟩ 0 hp : ↥(Q2.reps ⟨25, by decide⟩)) : Coordinate 2)
        Q2.T67_25_2 = colFn colCert_67_25_0.D (m := 25) from colCert_67_25_0.bind2]
  exact alnAll_67_25_0 j hj hq

theorem leaf_67_25_1 (hp : 1 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 1 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp)) T67_25
      hfix67_25 hinj67_25 hcardT67_25
      (fun i => conj_mem_of_fixedPoints _ _ (T67_25 i) (hfix67_25 i) _)
      ⟨67, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 1 hp) Q2.T67_25_2 Q2.hfix67_25_2 Q2.hinj67_25_2
      Q2.hcardT67_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_25_2 i) (Q2.hfix67_25_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨25, by decide⟩ 1 (transLenTr ⟨25, by decide⟩ 1 hp) : ↥(reps ⟨25, by decide⟩)) : Coordinate 1)
        T67_25 = colFn colCert_67_25_1.D (m := 25) from colCert_67_25_1.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨25, by decide⟩ 1 hp : ↥(Q2.reps ⟨25, by decide⟩)) : Coordinate 2)
        Q2.T67_25_2 = colFn colCert_67_25_1.D (m := 25) from colCert_67_25_1.bind2]
  exact alnAll_67_25_1 j hj hq

theorem leaf_67_25_2 (hp : 2 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 2 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp)) T67_25
      hfix67_25 hinj67_25 hcardT67_25
      (fun i => conj_mem_of_fixedPoints _ _ (T67_25 i) (hfix67_25 i) _)
      ⟨67, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 2 hp) Q2.T67_25_2 Q2.hfix67_25_2 Q2.hinj67_25_2
      Q2.hcardT67_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_25_2 i) (Q2.hfix67_25_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨25, by decide⟩ 2 (transLenTr ⟨25, by decide⟩ 2 hp) : ↥(reps ⟨25, by decide⟩)) : Coordinate 1)
        T67_25 = colFn colCert_67_25_2.D (m := 25) from colCert_67_25_2.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨25, by decide⟩ 2 hp : ↥(Q2.reps ⟨25, by decide⟩)) : Coordinate 2)
        Q2.T67_25_2 = colFn colCert_67_25_2.D (m := 25) from colCert_67_25_2.bind2]
  exact alnAll_67_25_2 j hj hq

theorem leaf_67_25_3 (hp : 3 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 3 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp)) T67_25
      hfix67_25 hinj67_25 hcardT67_25
      (fun i => conj_mem_of_fixedPoints _ _ (T67_25 i) (hfix67_25 i) _)
      ⟨67, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 3 hp) Q2.T67_25_2 Q2.hfix67_25_2 Q2.hinj67_25_2
      Q2.hcardT67_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_25_2 i) (Q2.hfix67_25_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨25, by decide⟩ 3 (transLenTr ⟨25, by decide⟩ 3 hp) : ↥(reps ⟨25, by decide⟩)) : Coordinate 1)
        T67_25 = colFn colCert_67_25_3.D (m := 25) from colCert_67_25_3.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨25, by decide⟩ 3 hp : ↥(Q2.reps ⟨25, by decide⟩)) : Coordinate 2)
        Q2.T67_25_2 = colFn colCert_67_25_3.D (m := 25) from colCert_67_25_3.bind2]
  exact alnAll_67_25_3 j hj hq

theorem leaf_67_25_4 (hp : 4 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 4 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp)) T67_25
      hfix67_25 hinj67_25 hcardT67_25
      (fun i => conj_mem_of_fixedPoints _ _ (T67_25 i) (hfix67_25 i) _)
      ⟨67, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 4 hp) Q2.T67_25_2 Q2.hfix67_25_2 Q2.hinj67_25_2
      Q2.hcardT67_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_25_2 i) (Q2.hfix67_25_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨25, by decide⟩ 4 (transLenTr ⟨25, by decide⟩ 4 hp) : ↥(reps ⟨25, by decide⟩)) : Coordinate 1)
        T67_25 = colFn colCert_67_25_4.D (m := 25) from colCert_67_25_4.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨25, by decide⟩ 4 hp : ↥(Q2.reps ⟨25, by decide⟩)) : Coordinate 2)
        Q2.T67_25_2 = colFn colCert_67_25_4.D (m := 25) from colCert_67_25_4.bind2]
  exact alnAll_67_25_4 j hj hq

theorem leaf_67_25_5 (hp : 5 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 5 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp)) T67_25
      hfix67_25 hinj67_25 hcardT67_25
      (fun i => conj_mem_of_fixedPoints _ _ (T67_25 i) (hfix67_25 i) _)
      ⟨67, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 5 hp) Q2.T67_25_2 Q2.hfix67_25_2 Q2.hinj67_25_2
      Q2.hcardT67_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_25_2 i) (Q2.hfix67_25_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨25, by decide⟩ 5 (transLenTr ⟨25, by decide⟩ 5 hp) : ↥(reps ⟨25, by decide⟩)) : Coordinate 1)
        T67_25 = colFn colCert_67_25_5.D (m := 25) from colCert_67_25_5.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨25, by decide⟩ 5 hp : ↥(Q2.reps ⟨25, by decide⟩)) : Coordinate 2)
        Q2.T67_25_2 = colFn colCert_67_25_5.D (m := 25) from colCert_67_25_5.bind2]
  exact alnAll_67_25_5 j hj hq

theorem leaf_67_25_10 (hp : 10 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 10 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp)) T67_25
      hfix67_25 hinj67_25 hcardT67_25
      (fun i => conj_mem_of_fixedPoints _ _ (T67_25 i) (hfix67_25 i) _)
      ⟨67, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 10 hp) Q2.T67_25_2 Q2.hfix67_25_2 Q2.hinj67_25_2
      Q2.hcardT67_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_25_2 i) (Q2.hfix67_25_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨25, by decide⟩ 10 (transLenTr ⟨25, by decide⟩ 10 hp) : ↥(reps ⟨25, by decide⟩)) : Coordinate 1)
        T67_25 = colFn colCert_67_25_10.D (m := 25) from colCert_67_25_10.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨25, by decide⟩ 10 hp : ↥(Q2.reps ⟨25, by decide⟩)) : Coordinate 2)
        Q2.T67_25_2 = colFn colCert_67_25_10.D (m := 25) from colCert_67_25_10.bind2]
  exact alnAll_67_25_10 j hj hq

theorem leaf_67_25_15 (hp : 15 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 15 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp)) T67_25
      hfix67_25 hinj67_25 hcardT67_25
      (fun i => conj_mem_of_fixedPoints _ _ (T67_25 i) (hfix67_25 i) _)
      ⟨67, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 15 hp) Q2.T67_25_2 Q2.hfix67_25_2 Q2.hinj67_25_2
      Q2.hcardT67_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_25_2 i) (Q2.hfix67_25_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨25, by decide⟩ 15 (transLenTr ⟨25, by decide⟩ 15 hp) : ↥(reps ⟨25, by decide⟩)) : Coordinate 1)
        T67_25 = colFn colCert_67_25_15.D (m := 25) from colCert_67_25_15.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨25, by decide⟩ 15 hp : ↥(Q2.reps ⟨25, by decide⟩)) : Coordinate 2)
        Q2.T67_25_2 = colFn colCert_67_25_15.D (m := 25) from colCert_67_25_15.bind2]
  exact alnAll_67_25_15 j hj hq

theorem leaf_67_25_20 (hp : 20 < (Q2.transData.getD 25 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨25, by decide⟩ : Fin 148)) (colE2 ⟨25, by decide⟩ 20 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨25, by decide⟩ : Fin 148))
        (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨25, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp)) T67_25
      hfix67_25 hinj67_25 hcardT67_25
      (fun i => conj_mem_of_fixedPoints _ _ (T67_25 i) (hfix67_25 i) _)
      ⟨67, by decide⟩ ⟨25, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨25, by decide⟩ 20 hp) Q2.T67_25_2 Q2.hfix67_25_2 Q2.hinj67_25_2
      Q2.hcardT67_25_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_25_2 i) (Q2.hfix67_25_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨25, by decide⟩ 20 (transLenTr ⟨25, by decide⟩ 20 hp) : ↥(reps ⟨25, by decide⟩)) : Coordinate 1)
        T67_25 = colFn colCert_67_25_20.D (m := 25) from colCert_67_25_20.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨25, by decide⟩ 20 hp : ↥(Q2.reps ⟨25, by decide⟩)) : Coordinate 2)
        Q2.T67_25_2 = colFn colCert_67_25_20.D (m := 25) from colCert_67_25_20.bind2]
  exact alnAll_67_25_20 j hj hq

theorem leaf_67_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T67_30
      hfix67_30 hinj67_30 hcardT67_30
      (fun i => conj_mem_of_fixedPoints _ _ (T67_30 i) (hfix67_30 i) _)
      ⟨67, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T67_30_2 Q2.hfix67_30_2 Q2.hinj67_30_2
      Q2.hcardT67_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_30_2 i) (Q2.hfix67_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T67_30 = colFn colCert_67_30_0.D (m := 5) from colCert_67_30_0.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 0 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T67_30_2 = colFn colCert_67_30_0.D (m := 5) from colCert_67_30_0.bind2]
  exact alnAll_67_30_0 j hj hq

theorem leaf_67_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T67_30
      hfix67_30 hinj67_30 hcardT67_30
      (fun i => conj_mem_of_fixedPoints _ _ (T67_30 i) (hfix67_30 i) _)
      ⟨67, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T67_30_2 Q2.hfix67_30_2 Q2.hinj67_30_2
      Q2.hcardT67_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_30_2 i) (Q2.hfix67_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T67_30 = colFn colCert_67_30_1.D (m := 5) from colCert_67_30_1.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 1 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T67_30_2 = colFn colCert_67_30_1.D (m := 5) from colCert_67_30_1.bind2]
  exact alnAll_67_30_1 j hj hq

theorem leaf_67_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T67_30
      hfix67_30 hinj67_30 hcardT67_30
      (fun i => conj_mem_of_fixedPoints _ _ (T67_30 i) (hfix67_30 i) _)
      ⟨67, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T67_30_2 Q2.hfix67_30_2 Q2.hinj67_30_2
      Q2.hcardT67_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_30_2 i) (Q2.hfix67_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T67_30 = colFn colCert_67_30_2.D (m := 5) from colCert_67_30_2.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 2 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T67_30_2 = colFn colCert_67_30_2.D (m := 5) from colCert_67_30_2.bind2]
  exact alnAll_67_30_2 j hj hq

theorem leaf_67_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T67_30
      hfix67_30 hinj67_30 hcardT67_30
      (fun i => conj_mem_of_fixedPoints _ _ (T67_30 i) (hfix67_30 i) _)
      ⟨67, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T67_30_2 Q2.hfix67_30_2 Q2.hinj67_30_2
      Q2.hcardT67_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_30_2 i) (Q2.hfix67_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T67_30 = colFn colCert_67_30_3.D (m := 5) from colCert_67_30_3.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 3 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T67_30_2 = colFn colCert_67_30_3.D (m := 5) from colCert_67_30_3.bind2]
  exact alnAll_67_30_3 j hj hq

theorem leaf_67_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T67_30
      hfix67_30 hinj67_30 hcardT67_30
      (fun i => conj_mem_of_fixedPoints _ _ (T67_30 i) (hfix67_30 i) _)
      ⟨67, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T67_30_2 Q2.hfix67_30_2 Q2.hinj67_30_2
      Q2.hcardT67_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_30_2 i) (Q2.hfix67_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T67_30 = colFn colCert_67_30_4.D (m := 5) from colCert_67_30_4.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 4 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T67_30_2 = colFn colCert_67_30_4.D (m := 5) from colCert_67_30_4.bind2]
  exact alnAll_67_30_4 j hj hq

theorem leaf_67_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T67_30
      hfix67_30 hinj67_30 hcardT67_30
      (fun i => conj_mem_of_fixedPoints _ _ (T67_30 i) (hfix67_30 i) _)
      ⟨67, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T67_30_2 Q2.hfix67_30_2 Q2.hinj67_30_2
      Q2.hcardT67_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_30_2 i) (Q2.hfix67_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T67_30 = colFn colCertDiv_67_30_5.D1 (m := 5) from colCertDiv_67_30_5.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 5 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T67_30_2 = colFn colCertDiv_67_30_5.D2 (m := 5) from colCertDiv_67_30_5.bind2]
  exact alnAll_67_30_5 j hj hq

theorem leaf_67_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T67_30
      hfix67_30 hinj67_30 hcardT67_30
      (fun i => conj_mem_of_fixedPoints _ _ (T67_30 i) (hfix67_30 i) _)
      ⟨67, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T67_30_2 Q2.hfix67_30_2 Q2.hinj67_30_2
      Q2.hcardT67_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_30_2 i) (Q2.hfix67_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T67_30 = colFn colCertDiv_67_30_10.D1 (m := 5) from colCertDiv_67_30_10.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 10 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T67_30_2 = colFn colCertDiv_67_30_10.D2 (m := 5) from colCertDiv_67_30_10.bind2]
  exact alnAll_67_30_10 j hj hq

theorem leaf_67_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T67_30
      hfix67_30 hinj67_30 hcardT67_30
      (fun i => conj_mem_of_fixedPoints _ _ (T67_30 i) (hfix67_30 i) _)
      ⟨67, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T67_30_2 Q2.hfix67_30_2 Q2.hinj67_30_2
      Q2.hcardT67_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_30_2 i) (Q2.hfix67_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T67_30 = colFn colCertDiv_67_30_15.D1 (m := 5) from colCertDiv_67_30_15.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 15 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T67_30_2 = colFn colCertDiv_67_30_15.D2 (m := 5) from colCertDiv_67_30_15.bind2]
  exact alnAll_67_30_15 j hj hq

theorem leaf_67_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T67_30
      hfix67_30 hinj67_30 hcardT67_30
      (fun i => conj_mem_of_fixedPoints _ _ (T67_30 i) (hfix67_30 i) _)
      ⟨67, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T67_30_2 Q2.hfix67_30_2 Q2.hinj67_30_2
      Q2.hcardT67_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_30_2 i) (Q2.hfix67_30_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp) : ↥(reps ⟨30, by decide⟩)) : Coordinate 1)
        T67_30 = colFn colCertDiv_67_30_20.D1 (m := 5) from colCertDiv_67_30_20.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨30, by decide⟩ 20 hp : ↥(Q2.reps ⟨30, by decide⟩)) : Coordinate 2)
        Q2.T67_30_2 = colFn colCertDiv_67_30_20.D2 (m := 5) from colCertDiv_67_30_20.bind2]
  exact alnAll_67_30_20 j hj hq

theorem leaf_67_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T67_35
      hfix67_35 hinj67_35 hcardT67_35
      (fun i => conj_mem_of_fixedPoints _ _ (T67_35 i) (hfix67_35 i) _)
      ⟨67, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T67_35_2 Q2.hfix67_35_2 Q2.hinj67_35_2
      Q2.hcardT67_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_35_2 i) (Q2.hfix67_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T67_35 = colFn colCert_67_35_0.D (m := 5) from colCert_67_35_0.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 0 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T67_35_2 = colFn colCert_67_35_0.D (m := 5) from colCert_67_35_0.bind2]
  exact alnAll_67_35_0 j hj hq

theorem leaf_67_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T67_35
      hfix67_35 hinj67_35 hcardT67_35
      (fun i => conj_mem_of_fixedPoints _ _ (T67_35 i) (hfix67_35 i) _)
      ⟨67, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T67_35_2 Q2.hfix67_35_2 Q2.hinj67_35_2
      Q2.hcardT67_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_35_2 i) (Q2.hfix67_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T67_35 = colFn colCert_67_35_1.D (m := 5) from colCert_67_35_1.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 1 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T67_35_2 = colFn colCert_67_35_1.D (m := 5) from colCert_67_35_1.bind2]
  exact alnAll_67_35_1 j hj hq

theorem leaf_67_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T67_35
      hfix67_35 hinj67_35 hcardT67_35
      (fun i => conj_mem_of_fixedPoints _ _ (T67_35 i) (hfix67_35 i) _)
      ⟨67, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T67_35_2 Q2.hfix67_35_2 Q2.hinj67_35_2
      Q2.hcardT67_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_35_2 i) (Q2.hfix67_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T67_35 = colFn colCert_67_35_2.D (m := 5) from colCert_67_35_2.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 2 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T67_35_2 = colFn colCert_67_35_2.D (m := 5) from colCert_67_35_2.bind2]
  exact alnAll_67_35_2 j hj hq

theorem leaf_67_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T67_35
      hfix67_35 hinj67_35 hcardT67_35
      (fun i => conj_mem_of_fixedPoints _ _ (T67_35 i) (hfix67_35 i) _)
      ⟨67, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T67_35_2 Q2.hfix67_35_2 Q2.hinj67_35_2
      Q2.hcardT67_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_35_2 i) (Q2.hfix67_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T67_35 = colFn colCert_67_35_3.D (m := 5) from colCert_67_35_3.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 3 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T67_35_2 = colFn colCert_67_35_3.D (m := 5) from colCert_67_35_3.bind2]
  exact alnAll_67_35_3 j hj hq

theorem leaf_67_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T67_35
      hfix67_35 hinj67_35 hcardT67_35
      (fun i => conj_mem_of_fixedPoints _ _ (T67_35 i) (hfix67_35 i) _)
      ⟨67, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T67_35_2 Q2.hfix67_35_2 Q2.hinj67_35_2
      Q2.hcardT67_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_35_2 i) (Q2.hfix67_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T67_35 = colFn colCert_67_35_4.D (m := 5) from colCert_67_35_4.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 4 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T67_35_2 = colFn colCert_67_35_4.D (m := 5) from colCert_67_35_4.bind2]
  exact alnAll_67_35_4 j hj hq

theorem leaf_67_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T67_35
      hfix67_35 hinj67_35 hcardT67_35
      (fun i => conj_mem_of_fixedPoints _ _ (T67_35 i) (hfix67_35 i) _)
      ⟨67, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T67_35_2 Q2.hfix67_35_2 Q2.hinj67_35_2
      Q2.hcardT67_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_35_2 i) (Q2.hfix67_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T67_35 = colFn colCertDiv_67_35_5.D1 (m := 5) from colCertDiv_67_35_5.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 5 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T67_35_2 = colFn colCertDiv_67_35_5.D2 (m := 5) from colCertDiv_67_35_5.bind2]
  exact alnAll_67_35_5 j hj hq

theorem leaf_67_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T67_35
      hfix67_35 hinj67_35 hcardT67_35
      (fun i => conj_mem_of_fixedPoints _ _ (T67_35 i) (hfix67_35 i) _)
      ⟨67, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T67_35_2 Q2.hfix67_35_2 Q2.hinj67_35_2
      Q2.hcardT67_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_35_2 i) (Q2.hfix67_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T67_35 = colFn colCertDiv_67_35_10.D1 (m := 5) from colCertDiv_67_35_10.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 10 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T67_35_2 = colFn colCertDiv_67_35_10.D2 (m := 5) from colCertDiv_67_35_10.bind2]
  exact alnAll_67_35_10 j hj hq

theorem leaf_67_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T67_35
      hfix67_35 hinj67_35 hcardT67_35
      (fun i => conj_mem_of_fixedPoints _ _ (T67_35 i) (hfix67_35 i) _)
      ⟨67, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T67_35_2 Q2.hfix67_35_2 Q2.hinj67_35_2
      Q2.hcardT67_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_35_2 i) (Q2.hfix67_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T67_35 = colFn colCertDiv_67_35_15.D1 (m := 5) from colCertDiv_67_35_15.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 15 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T67_35_2 = colFn colCertDiv_67_35_15.D2 (m := 5) from colCertDiv_67_35_15.bind2]
  exact alnAll_67_35_15 j hj hq

theorem leaf_67_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T67_35
      hfix67_35 hinj67_35 hcardT67_35
      (fun i => conj_mem_of_fixedPoints _ _ (T67_35 i) (hfix67_35 i) _)
      ⟨67, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T67_35_2 Q2.hfix67_35_2 Q2.hinj67_35_2
      Q2.hcardT67_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_35_2 i) (Q2.hfix67_35_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp) : ↥(reps ⟨35, by decide⟩)) : Coordinate 1)
        T67_35 = colFn colCertDiv_67_35_20.D1 (m := 5) from colCertDiv_67_35_20.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨35, by decide⟩ 20 hp : ↥(Q2.reps ⟨35, by decide⟩)) : Coordinate 2)
        Q2.T67_35_2 = colFn colCertDiv_67_35_20.D2 (m := 5) from colCertDiv_67_35_20.bind2]
  exact alnAll_67_35_20 j hj hq

theorem leaf_67_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T67_40
      hfix67_40 hinj67_40 hcardT67_40
      (fun i => conj_mem_of_fixedPoints _ _ (T67_40 i) (hfix67_40 i) _)
      ⟨67, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T67_40_2 Q2.hfix67_40_2 Q2.hinj67_40_2
      Q2.hcardT67_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_40_2 i) (Q2.hfix67_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T67_40 = colFn colCert_67_40_0.D (m := 5) from colCert_67_40_0.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 0 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T67_40_2 = colFn colCert_67_40_0.D (m := 5) from colCert_67_40_0.bind2]
  exact alnAll_67_40_0 j hj hq

theorem leaf_67_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T67_40
      hfix67_40 hinj67_40 hcardT67_40
      (fun i => conj_mem_of_fixedPoints _ _ (T67_40 i) (hfix67_40 i) _)
      ⟨67, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T67_40_2 Q2.hfix67_40_2 Q2.hinj67_40_2
      Q2.hcardT67_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_40_2 i) (Q2.hfix67_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T67_40 = colFn colCert_67_40_1.D (m := 5) from colCert_67_40_1.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 1 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T67_40_2 = colFn colCert_67_40_1.D (m := 5) from colCert_67_40_1.bind2]
  exact alnAll_67_40_1 j hj hq

theorem leaf_67_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T67_40
      hfix67_40 hinj67_40 hcardT67_40
      (fun i => conj_mem_of_fixedPoints _ _ (T67_40 i) (hfix67_40 i) _)
      ⟨67, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T67_40_2 Q2.hfix67_40_2 Q2.hinj67_40_2
      Q2.hcardT67_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_40_2 i) (Q2.hfix67_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T67_40 = colFn colCert_67_40_2.D (m := 5) from colCert_67_40_2.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 2 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T67_40_2 = colFn colCert_67_40_2.D (m := 5) from colCert_67_40_2.bind2]
  exact alnAll_67_40_2 j hj hq

theorem leaf_67_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T67_40
      hfix67_40 hinj67_40 hcardT67_40
      (fun i => conj_mem_of_fixedPoints _ _ (T67_40 i) (hfix67_40 i) _)
      ⟨67, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T67_40_2 Q2.hfix67_40_2 Q2.hinj67_40_2
      Q2.hcardT67_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_40_2 i) (Q2.hfix67_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T67_40 = colFn colCert_67_40_3.D (m := 5) from colCert_67_40_3.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 3 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T67_40_2 = colFn colCert_67_40_3.D (m := 5) from colCert_67_40_3.bind2]
  exact alnAll_67_40_3 j hj hq

theorem leaf_67_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T67_40
      hfix67_40 hinj67_40 hcardT67_40
      (fun i => conj_mem_of_fixedPoints _ _ (T67_40 i) (hfix67_40 i) _)
      ⟨67, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T67_40_2 Q2.hfix67_40_2 Q2.hinj67_40_2
      Q2.hcardT67_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_40_2 i) (Q2.hfix67_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T67_40 = colFn colCert_67_40_4.D (m := 5) from colCert_67_40_4.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 4 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T67_40_2 = colFn colCert_67_40_4.D (m := 5) from colCert_67_40_4.bind2]
  exact alnAll_67_40_4 j hj hq

theorem leaf_67_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T67_40
      hfix67_40 hinj67_40 hcardT67_40
      (fun i => conj_mem_of_fixedPoints _ _ (T67_40 i) (hfix67_40 i) _)
      ⟨67, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T67_40_2 Q2.hfix67_40_2 Q2.hinj67_40_2
      Q2.hcardT67_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_40_2 i) (Q2.hfix67_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T67_40 = colFn colCertDiv_67_40_5.D1 (m := 5) from colCertDiv_67_40_5.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 5 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T67_40_2 = colFn colCertDiv_67_40_5.D2 (m := 5) from colCertDiv_67_40_5.bind2]
  exact alnAll_67_40_5 j hj hq

theorem leaf_67_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T67_40
      hfix67_40 hinj67_40 hcardT67_40
      (fun i => conj_mem_of_fixedPoints _ _ (T67_40 i) (hfix67_40 i) _)
      ⟨67, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T67_40_2 Q2.hfix67_40_2 Q2.hinj67_40_2
      Q2.hcardT67_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_40_2 i) (Q2.hfix67_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T67_40 = colFn colCertDiv_67_40_10.D1 (m := 5) from colCertDiv_67_40_10.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 10 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T67_40_2 = colFn colCertDiv_67_40_10.D2 (m := 5) from colCertDiv_67_40_10.bind2]
  exact alnAll_67_40_10 j hj hq

theorem leaf_67_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T67_40
      hfix67_40 hinj67_40 hcardT67_40
      (fun i => conj_mem_of_fixedPoints _ _ (T67_40 i) (hfix67_40 i) _)
      ⟨67, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T67_40_2 Q2.hfix67_40_2 Q2.hinj67_40_2
      Q2.hcardT67_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_40_2 i) (Q2.hfix67_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T67_40 = colFn colCertDiv_67_40_15.D1 (m := 5) from colCertDiv_67_40_15.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 15 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T67_40_2 = colFn colCertDiv_67_40_15.D2 (m := 5) from colCertDiv_67_40_15.bind2]
  exact alnAll_67_40_15 j hj hq

theorem leaf_67_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T67_40
      hfix67_40 hinj67_40 hcardT67_40
      (fun i => conj_mem_of_fixedPoints _ _ (T67_40 i) (hfix67_40 i) _)
      ⟨67, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T67_40_2 Q2.hfix67_40_2 Q2.hinj67_40_2
      Q2.hcardT67_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_40_2 i) (Q2.hfix67_40_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp) : ↥(reps ⟨40, by decide⟩)) : Coordinate 1)
        T67_40 = colFn colCertDiv_67_40_20.D1 (m := 5) from colCertDiv_67_40_20.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨40, by decide⟩ 20 hp : ↥(Q2.reps ⟨40, by decide⟩)) : Coordinate 2)
        Q2.T67_40_2 = colFn colCertDiv_67_40_20.D2 (m := 5) from colCertDiv_67_40_20.bind2]
  exact alnAll_67_40_20 j hj hq

theorem leaf_67_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T67_45
      hfix67_45 hinj67_45 hcardT67_45
      (fun i => conj_mem_of_fixedPoints _ _ (T67_45 i) (hfix67_45 i) _)
      ⟨67, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T67_45_2 Q2.hfix67_45_2 Q2.hinj67_45_2
      Q2.hcardT67_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_45_2 i) (Q2.hfix67_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T67_45 = colFn colCert_67_45_0.D (m := 5) from colCert_67_45_0.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 0 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T67_45_2 = colFn colCert_67_45_0.D (m := 5) from colCert_67_45_0.bind2]
  exact alnAll_67_45_0 j hj hq

theorem leaf_67_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T67_45
      hfix67_45 hinj67_45 hcardT67_45
      (fun i => conj_mem_of_fixedPoints _ _ (T67_45 i) (hfix67_45 i) _)
      ⟨67, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T67_45_2 Q2.hfix67_45_2 Q2.hinj67_45_2
      Q2.hcardT67_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_45_2 i) (Q2.hfix67_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T67_45 = colFn colCert_67_45_1.D (m := 5) from colCert_67_45_1.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 1 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T67_45_2 = colFn colCert_67_45_1.D (m := 5) from colCert_67_45_1.bind2]
  exact alnAll_67_45_1 j hj hq

theorem leaf_67_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T67_45
      hfix67_45 hinj67_45 hcardT67_45
      (fun i => conj_mem_of_fixedPoints _ _ (T67_45 i) (hfix67_45 i) _)
      ⟨67, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T67_45_2 Q2.hfix67_45_2 Q2.hinj67_45_2
      Q2.hcardT67_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_45_2 i) (Q2.hfix67_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T67_45 = colFn colCert_67_45_2.D (m := 5) from colCert_67_45_2.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 2 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T67_45_2 = colFn colCert_67_45_2.D (m := 5) from colCert_67_45_2.bind2]
  exact alnAll_67_45_2 j hj hq

theorem leaf_67_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T67_45
      hfix67_45 hinj67_45 hcardT67_45
      (fun i => conj_mem_of_fixedPoints _ _ (T67_45 i) (hfix67_45 i) _)
      ⟨67, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T67_45_2 Q2.hfix67_45_2 Q2.hinj67_45_2
      Q2.hcardT67_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_45_2 i) (Q2.hfix67_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T67_45 = colFn colCert_67_45_3.D (m := 5) from colCert_67_45_3.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 3 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T67_45_2 = colFn colCert_67_45_3.D (m := 5) from colCert_67_45_3.bind2]
  exact alnAll_67_45_3 j hj hq

theorem leaf_67_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T67_45
      hfix67_45 hinj67_45 hcardT67_45
      (fun i => conj_mem_of_fixedPoints _ _ (T67_45 i) (hfix67_45 i) _)
      ⟨67, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T67_45_2 Q2.hfix67_45_2 Q2.hinj67_45_2
      Q2.hcardT67_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_45_2 i) (Q2.hfix67_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T67_45 = colFn colCert_67_45_4.D (m := 5) from colCert_67_45_4.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 4 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T67_45_2 = colFn colCert_67_45_4.D (m := 5) from colCert_67_45_4.bind2]
  exact alnAll_67_45_4 j hj hq

theorem leaf_67_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T67_45
      hfix67_45 hinj67_45 hcardT67_45
      (fun i => conj_mem_of_fixedPoints _ _ (T67_45 i) (hfix67_45 i) _)
      ⟨67, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T67_45_2 Q2.hfix67_45_2 Q2.hinj67_45_2
      Q2.hcardT67_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_45_2 i) (Q2.hfix67_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T67_45 = colFn colCertDiv_67_45_5.D1 (m := 5) from colCertDiv_67_45_5.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 5 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T67_45_2 = colFn colCertDiv_67_45_5.D2 (m := 5) from colCertDiv_67_45_5.bind2]
  exact alnAll_67_45_5 j hj hq

theorem leaf_67_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T67_45
      hfix67_45 hinj67_45 hcardT67_45
      (fun i => conj_mem_of_fixedPoints _ _ (T67_45 i) (hfix67_45 i) _)
      ⟨67, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T67_45_2 Q2.hfix67_45_2 Q2.hinj67_45_2
      Q2.hcardT67_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_45_2 i) (Q2.hfix67_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T67_45 = colFn colCertDiv_67_45_10.D1 (m := 5) from colCertDiv_67_45_10.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 10 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T67_45_2 = colFn colCertDiv_67_45_10.D2 (m := 5) from colCertDiv_67_45_10.bind2]
  exact alnAll_67_45_10 j hj hq

theorem leaf_67_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T67_45
      hfix67_45 hinj67_45 hcardT67_45
      (fun i => conj_mem_of_fixedPoints _ _ (T67_45 i) (hfix67_45 i) _)
      ⟨67, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T67_45_2 Q2.hfix67_45_2 Q2.hinj67_45_2
      Q2.hcardT67_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_45_2 i) (Q2.hfix67_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T67_45 = colFn colCertDiv_67_45_15.D1 (m := 5) from colCertDiv_67_45_15.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 15 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T67_45_2 = colFn colCertDiv_67_45_15.D2 (m := 5) from colCertDiv_67_45_15.bind2]
  exact alnAll_67_45_15 j hj hq

theorem leaf_67_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T67_45
      hfix67_45 hinj67_45 hcardT67_45
      (fun i => conj_mem_of_fixedPoints _ _ (T67_45 i) (hfix67_45 i) _)
      ⟨67, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T67_45_2 Q2.hfix67_45_2 Q2.hinj67_45_2
      Q2.hcardT67_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_45_2 i) (Q2.hfix67_45_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp) : ↥(reps ⟨45, by decide⟩)) : Coordinate 1)
        T67_45 = colFn colCertDiv_67_45_20.D1 (m := 5) from colCertDiv_67_45_20.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨45, by decide⟩ 20 hp : ↥(Q2.reps ⟨45, by decide⟩)) : Coordinate 2)
        Q2.T67_45_2 = colFn colCertDiv_67_45_20.D2 (m := 5) from colCertDiv_67_45_20.bind2]
  exact alnAll_67_45_20 j hj hq

theorem leaf_67_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T67_50
      hfix67_50 hinj67_50 hcardT67_50
      (fun i => conj_mem_of_fixedPoints _ _ (T67_50 i) (hfix67_50 i) _)
      ⟨67, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T67_50_2 Q2.hfix67_50_2 Q2.hinj67_50_2
      Q2.hcardT67_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_50_2 i) (Q2.hfix67_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T67_50 = colFn colCert_67_50_0.D (m := 5) from colCert_67_50_0.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 0 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T67_50_2 = colFn colCert_67_50_0.D (m := 5) from colCert_67_50_0.bind2]
  exact alnAll_67_50_0 j hj hq

theorem leaf_67_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T67_50
      hfix67_50 hinj67_50 hcardT67_50
      (fun i => conj_mem_of_fixedPoints _ _ (T67_50 i) (hfix67_50 i) _)
      ⟨67, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T67_50_2 Q2.hfix67_50_2 Q2.hinj67_50_2
      Q2.hcardT67_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_50_2 i) (Q2.hfix67_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T67_50 = colFn colCert_67_50_1.D (m := 5) from colCert_67_50_1.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 1 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T67_50_2 = colFn colCert_67_50_1.D (m := 5) from colCert_67_50_1.bind2]
  exact alnAll_67_50_1 j hj hq

theorem leaf_67_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T67_50
      hfix67_50 hinj67_50 hcardT67_50
      (fun i => conj_mem_of_fixedPoints _ _ (T67_50 i) (hfix67_50 i) _)
      ⟨67, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T67_50_2 Q2.hfix67_50_2 Q2.hinj67_50_2
      Q2.hcardT67_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_50_2 i) (Q2.hfix67_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T67_50 = colFn colCert_67_50_2.D (m := 5) from colCert_67_50_2.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 2 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T67_50_2 = colFn colCert_67_50_2.D (m := 5) from colCert_67_50_2.bind2]
  exact alnAll_67_50_2 j hj hq

theorem leaf_67_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T67_50
      hfix67_50 hinj67_50 hcardT67_50
      (fun i => conj_mem_of_fixedPoints _ _ (T67_50 i) (hfix67_50 i) _)
      ⟨67, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T67_50_2 Q2.hfix67_50_2 Q2.hinj67_50_2
      Q2.hcardT67_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_50_2 i) (Q2.hfix67_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T67_50 = colFn colCert_67_50_3.D (m := 5) from colCert_67_50_3.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 3 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T67_50_2 = colFn colCert_67_50_3.D (m := 5) from colCert_67_50_3.bind2]
  exact alnAll_67_50_3 j hj hq

theorem leaf_67_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T67_50
      hfix67_50 hinj67_50 hcardT67_50
      (fun i => conj_mem_of_fixedPoints _ _ (T67_50 i) (hfix67_50 i) _)
      ⟨67, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T67_50_2 Q2.hfix67_50_2 Q2.hinj67_50_2
      Q2.hcardT67_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_50_2 i) (Q2.hfix67_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T67_50 = colFn colCert_67_50_4.D (m := 5) from colCert_67_50_4.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 4 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T67_50_2 = colFn colCert_67_50_4.D (m := 5) from colCert_67_50_4.bind2]
  exact alnAll_67_50_4 j hj hq

theorem leaf_67_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T67_50
      hfix67_50 hinj67_50 hcardT67_50
      (fun i => conj_mem_of_fixedPoints _ _ (T67_50 i) (hfix67_50 i) _)
      ⟨67, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T67_50_2 Q2.hfix67_50_2 Q2.hinj67_50_2
      Q2.hcardT67_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_50_2 i) (Q2.hfix67_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T67_50 = colFn colCertDiv_67_50_5.D1 (m := 5) from colCertDiv_67_50_5.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 5 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T67_50_2 = colFn colCertDiv_67_50_5.D2 (m := 5) from colCertDiv_67_50_5.bind2]
  exact alnAll_67_50_5 j hj hq

theorem leaf_67_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T67_50
      hfix67_50 hinj67_50 hcardT67_50
      (fun i => conj_mem_of_fixedPoints _ _ (T67_50 i) (hfix67_50 i) _)
      ⟨67, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T67_50_2 Q2.hfix67_50_2 Q2.hinj67_50_2
      Q2.hcardT67_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_50_2 i) (Q2.hfix67_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T67_50 = colFn colCertDiv_67_50_10.D1 (m := 5) from colCertDiv_67_50_10.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 10 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T67_50_2 = colFn colCertDiv_67_50_10.D2 (m := 5) from colCertDiv_67_50_10.bind2]
  exact alnAll_67_50_10 j hj hq

theorem leaf_67_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T67_50
      hfix67_50 hinj67_50 hcardT67_50
      (fun i => conj_mem_of_fixedPoints _ _ (T67_50 i) (hfix67_50 i) _)
      ⟨67, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T67_50_2 Q2.hfix67_50_2 Q2.hinj67_50_2
      Q2.hcardT67_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_50_2 i) (Q2.hfix67_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T67_50 = colFn colCertDiv_67_50_15.D1 (m := 5) from colCertDiv_67_50_15.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 15 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T67_50_2 = colFn colCertDiv_67_50_15.D2 (m := 5) from colCertDiv_67_50_15.bind2]
  exact alnAll_67_50_15 j hj hq

theorem leaf_67_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T67_50
      hfix67_50 hinj67_50 hcardT67_50
      (fun i => conj_mem_of_fixedPoints _ _ (T67_50 i) (hfix67_50 i) _)
      ⟨67, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T67_50_2 Q2.hfix67_50_2 Q2.hinj67_50_2
      Q2.hcardT67_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_50_2 i) (Q2.hfix67_50_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp) : ↥(reps ⟨50, by decide⟩)) : Coordinate 1)
        T67_50 = colFn colCertDiv_67_50_20.D1 (m := 5) from colCertDiv_67_50_20.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨50, by decide⟩ 20 hp : ↥(Q2.reps ⟨50, by decide⟩)) : Coordinate 2)
        Q2.T67_50_2 = colFn colCertDiv_67_50_20.D2 (m := 5) from colCertDiv_67_50_20.bind2]
  exact alnAll_67_50_20 j hj hq

theorem leaf_67_67_0 (hp : 0 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 0 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 0 (transLenTr ⟨67, by decide⟩ 0 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 0 (transLenTr ⟨67, by decide⟩ 0 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 0 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 0 (transLenTr ⟨67, by decide⟩ 0 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_0.D (m := 5) from colCert_67_67_0.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 0 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_0.D (m := 5) from colCert_67_67_0.bind2]
  exact alnAll_67_67_0 j hj hq

theorem leaf_67_67_1 (hp : 1 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 1 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 1 (transLenTr ⟨67, by decide⟩ 1 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 1 (transLenTr ⟨67, by decide⟩ 1 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 1 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 1 (transLenTr ⟨67, by decide⟩ 1 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_1.D (m := 5) from colCert_67_67_1.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 1 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_1.D (m := 5) from colCert_67_67_1.bind2]
  exact alnAll_67_67_1 j hj hq

theorem leaf_67_67_2 (hp : 2 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 2 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 2 (transLenTr ⟨67, by decide⟩ 2 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 2 (transLenTr ⟨67, by decide⟩ 2 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 2 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 2 (transLenTr ⟨67, by decide⟩ 2 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_2.D (m := 5) from colCert_67_67_2.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 2 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_2.D (m := 5) from colCert_67_67_2.bind2]
  exact alnAll_67_67_2 j hj hq

theorem leaf_67_67_3 (hp : 3 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 3 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 3 (transLenTr ⟨67, by decide⟩ 3 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 3 (transLenTr ⟨67, by decide⟩ 3 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 3 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 3 (transLenTr ⟨67, by decide⟩ 3 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_3.D (m := 5) from colCert_67_67_3.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 3 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_3.D (m := 5) from colCert_67_67_3.bind2]
  exact alnAll_67_67_3 j hj hq

theorem leaf_67_67_4 (hp : 4 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 4 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 4 (transLenTr ⟨67, by decide⟩ 4 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 4 (transLenTr ⟨67, by decide⟩ 4 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 4 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 4 (transLenTr ⟨67, by decide⟩ 4 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_4.D (m := 5) from colCert_67_67_4.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 4 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_4.D (m := 5) from colCert_67_67_4.bind2]
  exact alnAll_67_67_4 j hj hq

theorem leaf_67_67_5 (hp : 5 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 5 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 5 (transLenTr ⟨67, by decide⟩ 5 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 5 (transLenTr ⟨67, by decide⟩ 5 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 5 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 5 (transLenTr ⟨67, by decide⟩ 5 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_5.D (m := 5) from colCert_67_67_5.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 5 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_5.D (m := 5) from colCert_67_67_5.bind2]
  exact alnAll_67_67_5 j hj hq

theorem leaf_67_67_6 (hp : 6 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 6 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 6 (transLenTr ⟨67, by decide⟩ 6 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 6 (transLenTr ⟨67, by decide⟩ 6 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 6 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 6 (transLenTr ⟨67, by decide⟩ 6 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_6.D (m := 5) from colCert_67_67_6.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 6 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_6.D (m := 5) from colCert_67_67_6.bind2]
  exact alnAll_67_67_6 j hj hq

theorem leaf_67_67_7 (hp : 7 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 7 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 7 (transLenTr ⟨67, by decide⟩ 7 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 7 (transLenTr ⟨67, by decide⟩ 7 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 7 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 7 (transLenTr ⟨67, by decide⟩ 7 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_7.D (m := 5) from colCert_67_67_7.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 7 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_7.D (m := 5) from colCert_67_67_7.bind2]
  exact alnAll_67_67_7 j hj hq

theorem leaf_67_67_8 (hp : 8 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 8 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 8 (transLenTr ⟨67, by decide⟩ 8 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 8 (transLenTr ⟨67, by decide⟩ 8 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 8 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 8 (transLenTr ⟨67, by decide⟩ 8 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_8.D (m := 5) from colCert_67_67_8.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 8 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_8.D (m := 5) from colCert_67_67_8.bind2]
  exact alnAll_67_67_8 j hj hq

theorem leaf_67_67_9 (hp : 9 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 9 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 9 (transLenTr ⟨67, by decide⟩ 9 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 9 (transLenTr ⟨67, by decide⟩ 9 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 9 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 9 (transLenTr ⟨67, by decide⟩ 9 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_9.D (m := 5) from colCert_67_67_9.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 9 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_9.D (m := 5) from colCert_67_67_9.bind2]
  exact alnAll_67_67_9 j hj hq

theorem leaf_67_67_10 (hp : 10 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 10 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 10 (transLenTr ⟨67, by decide⟩ 10 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 10 (transLenTr ⟨67, by decide⟩ 10 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 10 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 10 (transLenTr ⟨67, by decide⟩ 10 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_10.D (m := 5) from colCert_67_67_10.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 10 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_10.D (m := 5) from colCert_67_67_10.bind2]
  exact alnAll_67_67_10 j hj hq

theorem leaf_67_67_11 (hp : 11 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 11 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 11 (transLenTr ⟨67, by decide⟩ 11 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 11 (transLenTr ⟨67, by decide⟩ 11 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 11 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 11 (transLenTr ⟨67, by decide⟩ 11 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_11.D (m := 5) from colCert_67_67_11.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 11 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_11.D (m := 5) from colCert_67_67_11.bind2]
  exact alnAll_67_67_11 j hj hq

theorem leaf_67_67_12 (hp : 12 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 12 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 12 (transLenTr ⟨67, by decide⟩ 12 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 12 (transLenTr ⟨67, by decide⟩ 12 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 12 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 12 (transLenTr ⟨67, by decide⟩ 12 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_12.D (m := 5) from colCert_67_67_12.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 12 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_12.D (m := 5) from colCert_67_67_12.bind2]
  exact alnAll_67_67_12 j hj hq

theorem leaf_67_67_13 (hp : 13 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 13 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 13 (transLenTr ⟨67, by decide⟩ 13 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 13 (transLenTr ⟨67, by decide⟩ 13 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 13 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 13 (transLenTr ⟨67, by decide⟩ 13 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_13.D (m := 5) from colCert_67_67_13.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 13 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_13.D (m := 5) from colCert_67_67_13.bind2]
  exact alnAll_67_67_13 j hj hq

theorem leaf_67_67_14 (hp : 14 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 14 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 14 (transLenTr ⟨67, by decide⟩ 14 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 14 (transLenTr ⟨67, by decide⟩ 14 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 14 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 14 (transLenTr ⟨67, by decide⟩ 14 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_14.D (m := 5) from colCert_67_67_14.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 14 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_14.D (m := 5) from colCert_67_67_14.bind2]
  exact alnAll_67_67_14 j hj hq

theorem leaf_67_67_15 (hp : 15 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 15 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 15 (transLenTr ⟨67, by decide⟩ 15 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 15 (transLenTr ⟨67, by decide⟩ 15 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 15 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 15 (transLenTr ⟨67, by decide⟩ 15 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_15.D (m := 5) from colCert_67_67_15.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 15 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_15.D (m := 5) from colCert_67_67_15.bind2]
  exact alnAll_67_67_15 j hj hq

theorem leaf_67_67_16 (hp : 16 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 16 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 16 (transLenTr ⟨67, by decide⟩ 16 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 16 (transLenTr ⟨67, by decide⟩ 16 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 16 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 16 (transLenTr ⟨67, by decide⟩ 16 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_16.D (m := 5) from colCert_67_67_16.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 16 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_16.D (m := 5) from colCert_67_67_16.bind2]
  exact alnAll_67_67_16 j hj hq

theorem leaf_67_67_17 (hp : 17 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 17 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 17 (transLenTr ⟨67, by decide⟩ 17 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 17 (transLenTr ⟨67, by decide⟩ 17 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 17 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 17 (transLenTr ⟨67, by decide⟩ 17 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_17.D (m := 5) from colCert_67_67_17.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 17 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_17.D (m := 5) from colCert_67_67_17.bind2]
  exact alnAll_67_67_17 j hj hq

theorem leaf_67_67_18 (hp : 18 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 18 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 18 (transLenTr ⟨67, by decide⟩ 18 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 18 (transLenTr ⟨67, by decide⟩ 18 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 18 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 18 (transLenTr ⟨67, by decide⟩ 18 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_18.D (m := 5) from colCert_67_67_18.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 18 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_18.D (m := 5) from colCert_67_67_18.bind2]
  exact alnAll_67_67_18 j hj hq

theorem leaf_67_67_19 (hp : 19 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 19 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 19 (transLenTr ⟨67, by decide⟩ 19 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 19 (transLenTr ⟨67, by decide⟩ 19 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 19 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 19 (transLenTr ⟨67, by decide⟩ 19 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_19.D (m := 5) from colCert_67_67_19.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 19 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_19.D (m := 5) from colCert_67_67_19.bind2]
  exact alnAll_67_67_19 j hj hq

theorem leaf_67_67_20 (hp : 20 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 20 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 20 (transLenTr ⟨67, by decide⟩ 20 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 20 (transLenTr ⟨67, by decide⟩ 20 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 20 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 20 (transLenTr ⟨67, by decide⟩ 20 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_20.D (m := 5) from colCert_67_67_20.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 20 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_20.D (m := 5) from colCert_67_67_20.bind2]
  exact alnAll_67_67_20 j hj hq

theorem leaf_67_67_21 (hp : 21 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 21 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 21 (transLenTr ⟨67, by decide⟩ 21 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 21 (transLenTr ⟨67, by decide⟩ 21 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 21 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 21 (transLenTr ⟨67, by decide⟩ 21 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_21.D (m := 5) from colCert_67_67_21.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 21 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_21.D (m := 5) from colCert_67_67_21.bind2]
  exact alnAll_67_67_21 j hj hq

theorem leaf_67_67_22 (hp : 22 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 22 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 22 (transLenTr ⟨67, by decide⟩ 22 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 22 (transLenTr ⟨67, by decide⟩ 22 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 22 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 22 (transLenTr ⟨67, by decide⟩ 22 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_22.D (m := 5) from colCert_67_67_22.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 22 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_22.D (m := 5) from colCert_67_67_22.bind2]
  exact alnAll_67_67_22 j hj hq

theorem leaf_67_67_23 (hp : 23 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 23 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 23 (transLenTr ⟨67, by decide⟩ 23 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 23 (transLenTr ⟨67, by decide⟩ 23 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 23 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 23 (transLenTr ⟨67, by decide⟩ 23 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_23.D (m := 5) from colCert_67_67_23.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 23 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_23.D (m := 5) from colCert_67_67_23.bind2]
  exact alnAll_67_67_23 j hj hq

theorem leaf_67_67_24 (hp : 24 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 24 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 24 (transLenTr ⟨67, by decide⟩ 24 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 24 (transLenTr ⟨67, by decide⟩ 24 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 24 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 24 (transLenTr ⟨67, by decide⟩ 24 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_24.D (m := 5) from colCert_67_67_24.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 24 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_24.D (m := 5) from colCert_67_67_24.bind2]
  exact alnAll_67_67_24 j hj hq

theorem leaf_67_67_25 (hp : 25 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 25 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 25 (transLenTr ⟨67, by decide⟩ 25 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 25 (transLenTr ⟨67, by decide⟩ 25 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 25 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 25 (transLenTr ⟨67, by decide⟩ 25 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_25.D (m := 5) from colCert_67_67_25.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 25 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_25.D (m := 5) from colCert_67_67_25.bind2]
  exact alnAll_67_67_25 j hj hq

theorem leaf_67_67_30 (hp : 30 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 30 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 30 (transLenTr ⟨67, by decide⟩ 30 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 30 (transLenTr ⟨67, by decide⟩ 30 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 30 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 30 (transLenTr ⟨67, by decide⟩ 30 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_30.D (m := 5) from colCert_67_67_30.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 30 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_30.D (m := 5) from colCert_67_67_30.bind2]
  exact alnAll_67_67_30 j hj hq

theorem leaf_67_67_35 (hp : 35 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 35 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 35 (transLenTr ⟨67, by decide⟩ 35 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 35 (transLenTr ⟨67, by decide⟩ 35 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 35 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 35 (transLenTr ⟨67, by decide⟩ 35 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_35.D (m := 5) from colCert_67_67_35.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 35 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_35.D (m := 5) from colCert_67_67_35.bind2]
  exact alnAll_67_67_35 j hj hq

theorem leaf_67_67_40 (hp : 40 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 40 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 40 (transLenTr ⟨67, by decide⟩ 40 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 40 (transLenTr ⟨67, by decide⟩ 40 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 40 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 40 (transLenTr ⟨67, by decide⟩ 40 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_40.D (m := 5) from colCert_67_67_40.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 40 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_40.D (m := 5) from colCert_67_67_40.bind2]
  exact alnAll_67_67_40 j hj hq

theorem leaf_67_67_45 (hp : 45 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 45 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 45 (transLenTr ⟨67, by decide⟩ 45 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 45 (transLenTr ⟨67, by decide⟩ 45 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 45 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 45 (transLenTr ⟨67, by decide⟩ 45 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_45.D (m := 5) from colCert_67_67_45.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 45 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_45.D (m := 5) from colCert_67_67_45.bind2]
  exact alnAll_67_67_45 j hj hq

theorem leaf_67_67_50 (hp : 50 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 50 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 50 (transLenTr ⟨67, by decide⟩ 50 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 50 (transLenTr ⟨67, by decide⟩ 50 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 50 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 50 (transLenTr ⟨67, by decide⟩ 50 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_50.D (m := 5) from colCert_67_67_50.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 50 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_50.D (m := 5) from colCert_67_67_50.bind2]
  exact alnAll_67_67_50 j hj hq

theorem leaf_67_67_55 (hp : 55 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 55 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 55 (transLenTr ⟨67, by decide⟩ 55 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 55 (transLenTr ⟨67, by decide⟩ 55 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 55 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 55 (transLenTr ⟨67, by decide⟩ 55 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_55.D (m := 5) from colCert_67_67_55.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 55 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_55.D (m := 5) from colCert_67_67_55.bind2]
  exact alnAll_67_67_55 j hj hq

theorem leaf_67_67_60 (hp : 60 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 60 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 60 (transLenTr ⟨67, by decide⟩ 60 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 60 (transLenTr ⟨67, by decide⟩ 60 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 60 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 60 (transLenTr ⟨67, by decide⟩ 60 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_60.D (m := 5) from colCert_67_67_60.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 60 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_60.D (m := 5) from colCert_67_67_60.bind2]
  exact alnAll_67_67_60 j hj hq

theorem leaf_67_67_65 (hp : 65 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 65 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 65 (transLenTr ⟨67, by decide⟩ 65 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 65 (transLenTr ⟨67, by decide⟩ 65 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 65 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 65 (transLenTr ⟨67, by decide⟩ 65 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_65.D (m := 5) from colCert_67_67_65.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 65 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_65.D (m := 5) from colCert_67_67_65.bind2]
  exact alnAll_67_67_65 j hj hq

theorem leaf_67_67_70 (hp : 70 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 70 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 70 (transLenTr ⟨67, by decide⟩ 70 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 70 (transLenTr ⟨67, by decide⟩ 70 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 70 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 70 (transLenTr ⟨67, by decide⟩ 70 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_70.D (m := 5) from colCert_67_67_70.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 70 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_70.D (m := 5) from colCert_67_67_70.bind2]
  exact alnAll_67_67_70 j hj hq

theorem leaf_67_67_75 (hp : 75 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 75 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 75 (transLenTr ⟨67, by decide⟩ 75 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 75 (transLenTr ⟨67, by decide⟩ 75 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 75 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 75 (transLenTr ⟨67, by decide⟩ 75 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_75.D (m := 5) from colCert_67_67_75.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 75 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_75.D (m := 5) from colCert_67_67_75.bind2]
  exact alnAll_67_67_75 j hj hq

theorem leaf_67_67_80 (hp : 80 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 80 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 80 (transLenTr ⟨67, by decide⟩ 80 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 80 (transLenTr ⟨67, by decide⟩ 80 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 80 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 80 (transLenTr ⟨67, by decide⟩ 80 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_80.D (m := 5) from colCert_67_67_80.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 80 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_80.D (m := 5) from colCert_67_67_80.bind2]
  exact alnAll_67_67_80 j hj hq

theorem leaf_67_67_85 (hp : 85 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 85 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 85 (transLenTr ⟨67, by decide⟩ 85 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 85 (transLenTr ⟨67, by decide⟩ 85 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 85 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 85 (transLenTr ⟨67, by decide⟩ 85 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_85.D (m := 5) from colCert_67_67_85.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 85 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_85.D (m := 5) from colCert_67_67_85.bind2]
  exact alnAll_67_67_85 j hj hq

theorem leaf_67_67_90 (hp : 90 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 90 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 90 (transLenTr ⟨67, by decide⟩ 90 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 90 (transLenTr ⟨67, by decide⟩ 90 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 90 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 90 (transLenTr ⟨67, by decide⟩ 90 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_90.D (m := 5) from colCert_67_67_90.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 90 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_90.D (m := 5) from colCert_67_67_90.bind2]
  exact alnAll_67_67_90 j hj hq

theorem leaf_67_67_95 (hp : 95 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 95 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 95 (transLenTr ⟨67, by decide⟩ 95 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 95 (transLenTr ⟨67, by decide⟩ 95 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 95 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 95 (transLenTr ⟨67, by decide⟩ 95 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_95.D (m := 5) from colCert_67_67_95.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 95 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_95.D (m := 5) from colCert_67_67_95.bind2]
  exact alnAll_67_67_95 j hj hq

theorem leaf_67_67_100 (hp : 100 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 100 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 100 (transLenTr ⟨67, by decide⟩ 100 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 100 (transLenTr ⟨67, by decide⟩ 100 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 100 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 100 (transLenTr ⟨67, by decide⟩ 100 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_100.D (m := 5) from colCert_67_67_100.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 100 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_100.D (m := 5) from colCert_67_67_100.bind2]
  exact alnAll_67_67_100 j hj hq

theorem leaf_67_67_105 (hp : 105 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 105 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 105 (transLenTr ⟨67, by decide⟩ 105 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 105 (transLenTr ⟨67, by decide⟩ 105 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 105 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 105 (transLenTr ⟨67, by decide⟩ 105 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_105.D (m := 5) from colCert_67_67_105.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 105 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_105.D (m := 5) from colCert_67_67_105.bind2]
  exact alnAll_67_67_105 j hj hq

theorem leaf_67_67_110 (hp : 110 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 110 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 110 (transLenTr ⟨67, by decide⟩ 110 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 110 (transLenTr ⟨67, by decide⟩ 110 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 110 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 110 (transLenTr ⟨67, by decide⟩ 110 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_110.D (m := 5) from colCert_67_67_110.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 110 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_110.D (m := 5) from colCert_67_67_110.bind2]
  exact alnAll_67_67_110 j hj hq

theorem leaf_67_67_115 (hp : 115 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 115 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 115 (transLenTr ⟨67, by decide⟩ 115 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 115 (transLenTr ⟨67, by decide⟩ 115 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 115 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 115 (transLenTr ⟨67, by decide⟩ 115 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_115.D (m := 5) from colCert_67_67_115.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 115 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_115.D (m := 5) from colCert_67_67_115.bind2]
  exact alnAll_67_67_115 j hj hq

theorem leaf_67_67_120 (hp : 120 < (Q2.transData.getD 67 []).length)
    (j : Nat) (hj : j < (repChars.getD 67 []).length)
    (hq : (normIsRep.getD 67 []).getD j false = true) :
    species (Q2.reps (⟨67, by decide⟩ : Fin 148)) (colE2 ⟨67, by decide⟩ 120 hp)
        (rowE2 (⟨67, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨67, by decide⟩ : Fin 148))
        (colE1 ⟨67, by decide⟩ 120 (transLenTr ⟨67, by decide⟩ 120 hp))
        (rowE1 (⟨67, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨67, by decide⟩ : Fin 148) ⟨67, by decide⟩ _
      (validAt ⟨67, by decide⟩ (listedAt ⟨67, by decide⟩ hj))
      (colE1 ⟨67, by decide⟩ 120 (transLenTr ⟨67, by decide⟩ 120 hp)) T67_67
      hfix67_67 hinj67_67 hcardT67_67
      (fun i => conj_mem_of_fixedPoints _ _ (T67_67 i) (hfix67_67 i) _)
      ⟨67, by decide⟩ ⟨67, by decide⟩ _
      (Q2.validAt ⟨67, by decide⟩ (Q2.listedAt ⟨67, by decide⟩
        (alnCheck_rep ⟨67, by decide⟩ hj hq).1))
      (colE2 ⟨67, by decide⟩ 120 hp) Q2.T67_67_2 Q2.hfix67_67_2 Q2.hinj67_67_2
      Q2.hcardT67_67_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T67_67_2 i) (Q2.hfix67_67_2 i) _)
      ?_).symm
  rw [show colData1 (⟨67, by decide⟩ : Fin 148)
        ((colE1 ⟨67, by decide⟩ 120 (transLenTr ⟨67, by decide⟩ 120 hp) : ↥(reps ⟨67, by decide⟩)) : Coordinate 1)
        T67_67 = colFn colCert_67_67_120.D (m := 5) from colCert_67_67_120.bind1,
    show colData2 (⟨67, by decide⟩ : Fin 148)
        ((colE2 ⟨67, by decide⟩ 120 hp : ↥(Q2.reps ⟨67, by decide⟩)) : Coordinate 2)
        Q2.T67_67_2 = colFn colCert_67_67_120.D (m := 5) from colCert_67_67_120.bind2]
  exact alnAll_67_67_120 j hj hq

theorem leaf_68_6_0 (hp : 0 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 0 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 0 (transLenTr ⟨6, by decide⟩ 0 hp)) T68_6
      hfix68_6 hinj68_6 hcardT68_6
      (fun i => conj_mem_of_fixedPoints _ _ (T68_6 i) (hfix68_6 i) _)
      ⟨68, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 0 hp) Q2.T68_6_2 Q2.hfix68_6_2 Q2.hinj68_6_2
      Q2.hcardT68_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_6_2 i) (Q2.hfix68_6_2 i) _)
      colCert_68_6_0.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_6_1 (hp : 1 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 1 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 1 (transLenTr ⟨6, by decide⟩ 1 hp)) T68_6
      hfix68_6 hinj68_6 hcardT68_6
      (fun i => conj_mem_of_fixedPoints _ _ (T68_6 i) (hfix68_6 i) _)
      ⟨68, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 1 hp) Q2.T68_6_2 Q2.hfix68_6_2 Q2.hinj68_6_2
      Q2.hcardT68_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_6_2 i) (Q2.hfix68_6_2 i) _)
      colCert_68_6_1.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_6_2 (hp : 2 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 2 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 2 (transLenTr ⟨6, by decide⟩ 2 hp)) T68_6
      hfix68_6 hinj68_6 hcardT68_6
      (fun i => conj_mem_of_fixedPoints _ _ (T68_6 i) (hfix68_6 i) _)
      ⟨68, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 2 hp) Q2.T68_6_2 Q2.hfix68_6_2 Q2.hinj68_6_2
      Q2.hcardT68_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_6_2 i) (Q2.hfix68_6_2 i) _)
      colCert_68_6_2.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_6_3 (hp : 3 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 3 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 3 (transLenTr ⟨6, by decide⟩ 3 hp)) T68_6
      hfix68_6 hinj68_6 hcardT68_6
      (fun i => conj_mem_of_fixedPoints _ _ (T68_6 i) (hfix68_6 i) _)
      ⟨68, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 3 hp) Q2.T68_6_2 Q2.hfix68_6_2 Q2.hinj68_6_2
      Q2.hcardT68_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_6_2 i) (Q2.hfix68_6_2 i) _)
      colCert_68_6_3.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_6_4 (hp : 4 < (Q2.transData.getD 6 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨6, by decide⟩ : Fin 148)) (colE2 ⟨6, by decide⟩ 4 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨6, by decide⟩ : Fin 148))
        (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨6, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨6, by decide⟩ 4 (transLenTr ⟨6, by decide⟩ 4 hp)) T68_6
      hfix68_6 hinj68_6 hcardT68_6
      (fun i => conj_mem_of_fixedPoints _ _ (T68_6 i) (hfix68_6 i) _)
      ⟨68, by decide⟩ ⟨6, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨6, by decide⟩ 4 hp) Q2.T68_6_2 Q2.hfix68_6_2 Q2.hinj68_6_2
      Q2.hcardT68_6_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_6_2 i) (Q2.hfix68_6_2 i) _)
      colCert_68_6_4.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T68_12
      hfix68_12 hinj68_12 hcardT68_12
      (fun i => conj_mem_of_fixedPoints _ _ (T68_12 i) (hfix68_12 i) _)
      ⟨68, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T68_12_2 Q2.hfix68_12_2 Q2.hinj68_12_2
      Q2.hcardT68_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_12_2 i) (Q2.hfix68_12_2 i) _)
      colCert_68_12_0.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T68_12
      hfix68_12 hinj68_12 hcardT68_12
      (fun i => conj_mem_of_fixedPoints _ _ (T68_12 i) (hfix68_12 i) _)
      ⟨68, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T68_12_2 Q2.hfix68_12_2 Q2.hinj68_12_2
      Q2.hcardT68_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_12_2 i) (Q2.hfix68_12_2 i) _)
      colCert_68_12_1.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T68_12
      hfix68_12 hinj68_12 hcardT68_12
      (fun i => conj_mem_of_fixedPoints _ _ (T68_12 i) (hfix68_12 i) _)
      ⟨68, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T68_12_2 Q2.hfix68_12_2 Q2.hinj68_12_2
      Q2.hcardT68_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_12_2 i) (Q2.hfix68_12_2 i) _)
      colCert_68_12_2.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T68_12
      hfix68_12 hinj68_12 hcardT68_12
      (fun i => conj_mem_of_fixedPoints _ _ (T68_12 i) (hfix68_12 i) _)
      ⟨68, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T68_12_2 Q2.hfix68_12_2 Q2.hinj68_12_2
      Q2.hcardT68_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_12_2 i) (Q2.hfix68_12_2 i) _)
      colCert_68_12_3.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T68_12
      hfix68_12 hinj68_12 hcardT68_12
      (fun i => conj_mem_of_fixedPoints _ _ (T68_12 i) (hfix68_12 i) _)
      ⟨68, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T68_12_2 Q2.hfix68_12_2 Q2.hinj68_12_2
      Q2.hcardT68_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_12_2 i) (Q2.hfix68_12_2 i) _)
      colCert_68_12_4.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_24_0 (hp : 0 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 0 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 0 (transLenTr ⟨24, by decide⟩ 0 hp)) T68_24
      hfix68_24 hinj68_24 hcardT68_24
      (fun i => conj_mem_of_fixedPoints _ _ (T68_24 i) (hfix68_24 i) _)
      ⟨68, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 0 hp) Q2.T68_24_2 Q2.hfix68_24_2 Q2.hinj68_24_2
      Q2.hcardT68_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_24_2 i) (Q2.hfix68_24_2 i) _)
      colCert_68_24_0.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_24_1 (hp : 1 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 1 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 1 (transLenTr ⟨24, by decide⟩ 1 hp)) T68_24
      hfix68_24 hinj68_24 hcardT68_24
      (fun i => conj_mem_of_fixedPoints _ _ (T68_24 i) (hfix68_24 i) _)
      ⟨68, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 1 hp) Q2.T68_24_2 Q2.hfix68_24_2 Q2.hinj68_24_2
      Q2.hcardT68_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_24_2 i) (Q2.hfix68_24_2 i) _)
      colCert_68_24_1.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_24_2 (hp : 2 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 2 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 2 (transLenTr ⟨24, by decide⟩ 2 hp)) T68_24
      hfix68_24 hinj68_24 hcardT68_24
      (fun i => conj_mem_of_fixedPoints _ _ (T68_24 i) (hfix68_24 i) _)
      ⟨68, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 2 hp) Q2.T68_24_2 Q2.hfix68_24_2 Q2.hinj68_24_2
      Q2.hcardT68_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_24_2 i) (Q2.hfix68_24_2 i) _)
      colCert_68_24_2.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_24_3 (hp : 3 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 3 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 3 (transLenTr ⟨24, by decide⟩ 3 hp)) T68_24
      hfix68_24 hinj68_24 hcardT68_24
      (fun i => conj_mem_of_fixedPoints _ _ (T68_24 i) (hfix68_24 i) _)
      ⟨68, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 3 hp) Q2.T68_24_2 Q2.hfix68_24_2 Q2.hinj68_24_2
      Q2.hcardT68_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_24_2 i) (Q2.hfix68_24_2 i) _)
      colCert_68_24_3.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_24_4 (hp : 4 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 4 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 4 (transLenTr ⟨24, by decide⟩ 4 hp)) T68_24
      hfix68_24 hinj68_24 hcardT68_24
      (fun i => conj_mem_of_fixedPoints _ _ (T68_24 i) (hfix68_24 i) _)
      ⟨68, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 4 hp) Q2.T68_24_2 Q2.hfix68_24_2 Q2.hinj68_24_2
      Q2.hcardT68_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_24_2 i) (Q2.hfix68_24_2 i) _)
      colCert_68_24_4.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_24_5 (hp : 5 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 5 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 5 (transLenTr ⟨24, by decide⟩ 5 hp)) T68_24
      hfix68_24 hinj68_24 hcardT68_24
      (fun i => conj_mem_of_fixedPoints _ _ (T68_24 i) (hfix68_24 i) _)
      ⟨68, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 5 hp) Q2.T68_24_2 Q2.hfix68_24_2 Q2.hinj68_24_2
      Q2.hcardT68_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_24_2 i) (Q2.hfix68_24_2 i) _)
      colCert_68_24_5.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_24_10 (hp : 10 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 10 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 10 (transLenTr ⟨24, by decide⟩ 10 hp)) T68_24
      hfix68_24 hinj68_24 hcardT68_24
      (fun i => conj_mem_of_fixedPoints _ _ (T68_24 i) (hfix68_24 i) _)
      ⟨68, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 10 hp) Q2.T68_24_2 Q2.hfix68_24_2 Q2.hinj68_24_2
      Q2.hcardT68_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_24_2 i) (Q2.hfix68_24_2 i) _)
      colCert_68_24_10.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_24_15 (hp : 15 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 15 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 15 (transLenTr ⟨24, by decide⟩ 15 hp)) T68_24
      hfix68_24 hinj68_24 hcardT68_24
      (fun i => conj_mem_of_fixedPoints _ _ (T68_24 i) (hfix68_24 i) _)
      ⟨68, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 15 hp) Q2.T68_24_2 Q2.hfix68_24_2 Q2.hinj68_24_2
      Q2.hcardT68_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_24_2 i) (Q2.hfix68_24_2 i) _)
      colCert_68_24_15.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_24_20 (hp : 20 < (Q2.transData.getD 24 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨24, by decide⟩ : Fin 148)) (colE2 ⟨24, by decide⟩ 20 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨24, by decide⟩ : Fin 148))
        (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨24, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨24, by decide⟩ 20 (transLenTr ⟨24, by decide⟩ 20 hp)) T68_24
      hfix68_24 hinj68_24 hcardT68_24
      (fun i => conj_mem_of_fixedPoints _ _ (T68_24 i) (hfix68_24 i) _)
      ⟨68, by decide⟩ ⟨24, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨24, by decide⟩ 20 hp) Q2.T68_24_2 Q2.hfix68_24_2 Q2.hinj68_24_2
      Q2.hcardT68_24_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_24_2 i) (Q2.hfix68_24_2 i) _)
      colCert_68_24_20.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_30_0 (hp : 0 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 0 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 0 (transLenTr ⟨30, by decide⟩ 0 hp)) T68_30
      hfix68_30 hinj68_30 hcardT68_30
      (fun i => conj_mem_of_fixedPoints _ _ (T68_30 i) (hfix68_30 i) _)
      ⟨68, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 0 hp) Q2.T68_30_2 Q2.hfix68_30_2 Q2.hinj68_30_2
      Q2.hcardT68_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_30_2 i) (Q2.hfix68_30_2 i) _)
      colCert_68_30_0.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_30_1 (hp : 1 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 1 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 1 (transLenTr ⟨30, by decide⟩ 1 hp)) T68_30
      hfix68_30 hinj68_30 hcardT68_30
      (fun i => conj_mem_of_fixedPoints _ _ (T68_30 i) (hfix68_30 i) _)
      ⟨68, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 1 hp) Q2.T68_30_2 Q2.hfix68_30_2 Q2.hinj68_30_2
      Q2.hcardT68_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_30_2 i) (Q2.hfix68_30_2 i) _)
      colCert_68_30_1.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_30_2 (hp : 2 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 2 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 2 (transLenTr ⟨30, by decide⟩ 2 hp)) T68_30
      hfix68_30 hinj68_30 hcardT68_30
      (fun i => conj_mem_of_fixedPoints _ _ (T68_30 i) (hfix68_30 i) _)
      ⟨68, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 2 hp) Q2.T68_30_2 Q2.hfix68_30_2 Q2.hinj68_30_2
      Q2.hcardT68_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_30_2 i) (Q2.hfix68_30_2 i) _)
      colCert_68_30_2.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_30_3 (hp : 3 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 3 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 3 (transLenTr ⟨30, by decide⟩ 3 hp)) T68_30
      hfix68_30 hinj68_30 hcardT68_30
      (fun i => conj_mem_of_fixedPoints _ _ (T68_30 i) (hfix68_30 i) _)
      ⟨68, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 3 hp) Q2.T68_30_2 Q2.hfix68_30_2 Q2.hinj68_30_2
      Q2.hcardT68_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_30_2 i) (Q2.hfix68_30_2 i) _)
      colCert_68_30_3.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_30_4 (hp : 4 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 4 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 4 (transLenTr ⟨30, by decide⟩ 4 hp)) T68_30
      hfix68_30 hinj68_30 hcardT68_30
      (fun i => conj_mem_of_fixedPoints _ _ (T68_30 i) (hfix68_30 i) _)
      ⟨68, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 4 hp) Q2.T68_30_2 Q2.hfix68_30_2 Q2.hinj68_30_2
      Q2.hcardT68_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_30_2 i) (Q2.hfix68_30_2 i) _)
      colCert_68_30_4.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_30_5 (hp : 5 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 5 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 5 (transLenTr ⟨30, by decide⟩ 5 hp)) T68_30
      hfix68_30 hinj68_30 hcardT68_30
      (fun i => conj_mem_of_fixedPoints _ _ (T68_30 i) (hfix68_30 i) _)
      ⟨68, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 5 hp) Q2.T68_30_2 Q2.hfix68_30_2 Q2.hinj68_30_2
      Q2.hcardT68_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_30_2 i) (Q2.hfix68_30_2 i) _)
      colCert_68_30_5.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_30_10 (hp : 10 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 10 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 10 (transLenTr ⟨30, by decide⟩ 10 hp)) T68_30
      hfix68_30 hinj68_30 hcardT68_30
      (fun i => conj_mem_of_fixedPoints _ _ (T68_30 i) (hfix68_30 i) _)
      ⟨68, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 10 hp) Q2.T68_30_2 Q2.hfix68_30_2 Q2.hinj68_30_2
      Q2.hcardT68_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_30_2 i) (Q2.hfix68_30_2 i) _)
      colCert_68_30_10.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_30_15 (hp : 15 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 15 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 15 (transLenTr ⟨30, by decide⟩ 15 hp)) T68_30
      hfix68_30 hinj68_30 hcardT68_30
      (fun i => conj_mem_of_fixedPoints _ _ (T68_30 i) (hfix68_30 i) _)
      ⟨68, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 15 hp) Q2.T68_30_2 Q2.hfix68_30_2 Q2.hinj68_30_2
      Q2.hcardT68_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_30_2 i) (Q2.hfix68_30_2 i) _)
      colCert_68_30_15.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_30_20 (hp : 20 < (Q2.transData.getD 30 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨30, by decide⟩ : Fin 148)) (colE2 ⟨30, by decide⟩ 20 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨30, by decide⟩ : Fin 148))
        (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨30, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨30, by decide⟩ 20 (transLenTr ⟨30, by decide⟩ 20 hp)) T68_30
      hfix68_30 hinj68_30 hcardT68_30
      (fun i => conj_mem_of_fixedPoints _ _ (T68_30 i) (hfix68_30 i) _)
      ⟨68, by decide⟩ ⟨30, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨30, by decide⟩ 20 hp) Q2.T68_30_2 Q2.hfix68_30_2 Q2.hinj68_30_2
      Q2.hcardT68_30_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_30_2 i) (Q2.hfix68_30_2 i) _)
      colCert_68_30_20.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_35_0 (hp : 0 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 0 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 0 (transLenTr ⟨35, by decide⟩ 0 hp)) T68_35
      hfix68_35 hinj68_35 hcardT68_35
      (fun i => conj_mem_of_fixedPoints _ _ (T68_35 i) (hfix68_35 i) _)
      ⟨68, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 0 hp) Q2.T68_35_2 Q2.hfix68_35_2 Q2.hinj68_35_2
      Q2.hcardT68_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_35_2 i) (Q2.hfix68_35_2 i) _)
      colCert_68_35_0.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_35_1 (hp : 1 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 1 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 1 (transLenTr ⟨35, by decide⟩ 1 hp)) T68_35
      hfix68_35 hinj68_35 hcardT68_35
      (fun i => conj_mem_of_fixedPoints _ _ (T68_35 i) (hfix68_35 i) _)
      ⟨68, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 1 hp) Q2.T68_35_2 Q2.hfix68_35_2 Q2.hinj68_35_2
      Q2.hcardT68_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_35_2 i) (Q2.hfix68_35_2 i) _)
      colCert_68_35_1.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_35_2 (hp : 2 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 2 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 2 (transLenTr ⟨35, by decide⟩ 2 hp)) T68_35
      hfix68_35 hinj68_35 hcardT68_35
      (fun i => conj_mem_of_fixedPoints _ _ (T68_35 i) (hfix68_35 i) _)
      ⟨68, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 2 hp) Q2.T68_35_2 Q2.hfix68_35_2 Q2.hinj68_35_2
      Q2.hcardT68_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_35_2 i) (Q2.hfix68_35_2 i) _)
      colCert_68_35_2.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_35_3 (hp : 3 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 3 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 3 (transLenTr ⟨35, by decide⟩ 3 hp)) T68_35
      hfix68_35 hinj68_35 hcardT68_35
      (fun i => conj_mem_of_fixedPoints _ _ (T68_35 i) (hfix68_35 i) _)
      ⟨68, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 3 hp) Q2.T68_35_2 Q2.hfix68_35_2 Q2.hinj68_35_2
      Q2.hcardT68_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_35_2 i) (Q2.hfix68_35_2 i) _)
      colCert_68_35_3.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_35_4 (hp : 4 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 4 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 4 (transLenTr ⟨35, by decide⟩ 4 hp)) T68_35
      hfix68_35 hinj68_35 hcardT68_35
      (fun i => conj_mem_of_fixedPoints _ _ (T68_35 i) (hfix68_35 i) _)
      ⟨68, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 4 hp) Q2.T68_35_2 Q2.hfix68_35_2 Q2.hinj68_35_2
      Q2.hcardT68_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_35_2 i) (Q2.hfix68_35_2 i) _)
      colCert_68_35_4.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_35_5 (hp : 5 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 5 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 5 (transLenTr ⟨35, by decide⟩ 5 hp)) T68_35
      hfix68_35 hinj68_35 hcardT68_35
      (fun i => conj_mem_of_fixedPoints _ _ (T68_35 i) (hfix68_35 i) _)
      ⟨68, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 5 hp) Q2.T68_35_2 Q2.hfix68_35_2 Q2.hinj68_35_2
      Q2.hcardT68_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_35_2 i) (Q2.hfix68_35_2 i) _)
      colCert_68_35_5.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_35_10 (hp : 10 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 10 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 10 (transLenTr ⟨35, by decide⟩ 10 hp)) T68_35
      hfix68_35 hinj68_35 hcardT68_35
      (fun i => conj_mem_of_fixedPoints _ _ (T68_35 i) (hfix68_35 i) _)
      ⟨68, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 10 hp) Q2.T68_35_2 Q2.hfix68_35_2 Q2.hinj68_35_2
      Q2.hcardT68_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_35_2 i) (Q2.hfix68_35_2 i) _)
      colCert_68_35_10.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_35_15 (hp : 15 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 15 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 15 (transLenTr ⟨35, by decide⟩ 15 hp)) T68_35
      hfix68_35 hinj68_35 hcardT68_35
      (fun i => conj_mem_of_fixedPoints _ _ (T68_35 i) (hfix68_35 i) _)
      ⟨68, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 15 hp) Q2.T68_35_2 Q2.hfix68_35_2 Q2.hinj68_35_2
      Q2.hcardT68_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_35_2 i) (Q2.hfix68_35_2 i) _)
      colCert_68_35_15.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_35_20 (hp : 20 < (Q2.transData.getD 35 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨35, by decide⟩ : Fin 148)) (colE2 ⟨35, by decide⟩ 20 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨35, by decide⟩ : Fin 148))
        (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨35, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨35, by decide⟩ 20 (transLenTr ⟨35, by decide⟩ 20 hp)) T68_35
      hfix68_35 hinj68_35 hcardT68_35
      (fun i => conj_mem_of_fixedPoints _ _ (T68_35 i) (hfix68_35 i) _)
      ⟨68, by decide⟩ ⟨35, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨35, by decide⟩ 20 hp) Q2.T68_35_2 Q2.hfix68_35_2 Q2.hinj68_35_2
      Q2.hcardT68_35_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_35_2 i) (Q2.hfix68_35_2 i) _)
      colCert_68_35_20.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_40_0 (hp : 0 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 0 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 0 (transLenTr ⟨40, by decide⟩ 0 hp)) T68_40
      hfix68_40 hinj68_40 hcardT68_40
      (fun i => conj_mem_of_fixedPoints _ _ (T68_40 i) (hfix68_40 i) _)
      ⟨68, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 0 hp) Q2.T68_40_2 Q2.hfix68_40_2 Q2.hinj68_40_2
      Q2.hcardT68_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_40_2 i) (Q2.hfix68_40_2 i) _)
      colCert_68_40_0.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_40_1 (hp : 1 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 1 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 1 (transLenTr ⟨40, by decide⟩ 1 hp)) T68_40
      hfix68_40 hinj68_40 hcardT68_40
      (fun i => conj_mem_of_fixedPoints _ _ (T68_40 i) (hfix68_40 i) _)
      ⟨68, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 1 hp) Q2.T68_40_2 Q2.hfix68_40_2 Q2.hinj68_40_2
      Q2.hcardT68_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_40_2 i) (Q2.hfix68_40_2 i) _)
      colCert_68_40_1.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_40_2 (hp : 2 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 2 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 2 (transLenTr ⟨40, by decide⟩ 2 hp)) T68_40
      hfix68_40 hinj68_40 hcardT68_40
      (fun i => conj_mem_of_fixedPoints _ _ (T68_40 i) (hfix68_40 i) _)
      ⟨68, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 2 hp) Q2.T68_40_2 Q2.hfix68_40_2 Q2.hinj68_40_2
      Q2.hcardT68_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_40_2 i) (Q2.hfix68_40_2 i) _)
      colCert_68_40_2.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_40_3 (hp : 3 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 3 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 3 (transLenTr ⟨40, by decide⟩ 3 hp)) T68_40
      hfix68_40 hinj68_40 hcardT68_40
      (fun i => conj_mem_of_fixedPoints _ _ (T68_40 i) (hfix68_40 i) _)
      ⟨68, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 3 hp) Q2.T68_40_2 Q2.hfix68_40_2 Q2.hinj68_40_2
      Q2.hcardT68_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_40_2 i) (Q2.hfix68_40_2 i) _)
      colCert_68_40_3.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_40_4 (hp : 4 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 4 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 4 (transLenTr ⟨40, by decide⟩ 4 hp)) T68_40
      hfix68_40 hinj68_40 hcardT68_40
      (fun i => conj_mem_of_fixedPoints _ _ (T68_40 i) (hfix68_40 i) _)
      ⟨68, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 4 hp) Q2.T68_40_2 Q2.hfix68_40_2 Q2.hinj68_40_2
      Q2.hcardT68_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_40_2 i) (Q2.hfix68_40_2 i) _)
      colCert_68_40_4.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_40_5 (hp : 5 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 5 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 5 (transLenTr ⟨40, by decide⟩ 5 hp)) T68_40
      hfix68_40 hinj68_40 hcardT68_40
      (fun i => conj_mem_of_fixedPoints _ _ (T68_40 i) (hfix68_40 i) _)
      ⟨68, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 5 hp) Q2.T68_40_2 Q2.hfix68_40_2 Q2.hinj68_40_2
      Q2.hcardT68_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_40_2 i) (Q2.hfix68_40_2 i) _)
      colCert_68_40_5.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_40_10 (hp : 10 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 10 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 10 (transLenTr ⟨40, by decide⟩ 10 hp)) T68_40
      hfix68_40 hinj68_40 hcardT68_40
      (fun i => conj_mem_of_fixedPoints _ _ (T68_40 i) (hfix68_40 i) _)
      ⟨68, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 10 hp) Q2.T68_40_2 Q2.hfix68_40_2 Q2.hinj68_40_2
      Q2.hcardT68_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_40_2 i) (Q2.hfix68_40_2 i) _)
      colCert_68_40_10.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_40_15 (hp : 15 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 15 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 15 (transLenTr ⟨40, by decide⟩ 15 hp)) T68_40
      hfix68_40 hinj68_40 hcardT68_40
      (fun i => conj_mem_of_fixedPoints _ _ (T68_40 i) (hfix68_40 i) _)
      ⟨68, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 15 hp) Q2.T68_40_2 Q2.hfix68_40_2 Q2.hinj68_40_2
      Q2.hcardT68_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_40_2 i) (Q2.hfix68_40_2 i) _)
      colCert_68_40_15.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_40_20 (hp : 20 < (Q2.transData.getD 40 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨40, by decide⟩ : Fin 148)) (colE2 ⟨40, by decide⟩ 20 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨40, by decide⟩ : Fin 148))
        (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨40, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨40, by decide⟩ 20 (transLenTr ⟨40, by decide⟩ 20 hp)) T68_40
      hfix68_40 hinj68_40 hcardT68_40
      (fun i => conj_mem_of_fixedPoints _ _ (T68_40 i) (hfix68_40 i) _)
      ⟨68, by decide⟩ ⟨40, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨40, by decide⟩ 20 hp) Q2.T68_40_2 Q2.hfix68_40_2 Q2.hinj68_40_2
      Q2.hcardT68_40_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_40_2 i) (Q2.hfix68_40_2 i) _)
      colCert_68_40_20.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_45_0 (hp : 0 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 0 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 0 (transLenTr ⟨45, by decide⟩ 0 hp)) T68_45
      hfix68_45 hinj68_45 hcardT68_45
      (fun i => conj_mem_of_fixedPoints _ _ (T68_45 i) (hfix68_45 i) _)
      ⟨68, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 0 hp) Q2.T68_45_2 Q2.hfix68_45_2 Q2.hinj68_45_2
      Q2.hcardT68_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_45_2 i) (Q2.hfix68_45_2 i) _)
      colCert_68_45_0.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_45_1 (hp : 1 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 1 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 1 (transLenTr ⟨45, by decide⟩ 1 hp)) T68_45
      hfix68_45 hinj68_45 hcardT68_45
      (fun i => conj_mem_of_fixedPoints _ _ (T68_45 i) (hfix68_45 i) _)
      ⟨68, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 1 hp) Q2.T68_45_2 Q2.hfix68_45_2 Q2.hinj68_45_2
      Q2.hcardT68_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_45_2 i) (Q2.hfix68_45_2 i) _)
      colCert_68_45_1.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_45_2 (hp : 2 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 2 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 2 (transLenTr ⟨45, by decide⟩ 2 hp)) T68_45
      hfix68_45 hinj68_45 hcardT68_45
      (fun i => conj_mem_of_fixedPoints _ _ (T68_45 i) (hfix68_45 i) _)
      ⟨68, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 2 hp) Q2.T68_45_2 Q2.hfix68_45_2 Q2.hinj68_45_2
      Q2.hcardT68_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_45_2 i) (Q2.hfix68_45_2 i) _)
      colCert_68_45_2.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_45_3 (hp : 3 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 3 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 3 (transLenTr ⟨45, by decide⟩ 3 hp)) T68_45
      hfix68_45 hinj68_45 hcardT68_45
      (fun i => conj_mem_of_fixedPoints _ _ (T68_45 i) (hfix68_45 i) _)
      ⟨68, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 3 hp) Q2.T68_45_2 Q2.hfix68_45_2 Q2.hinj68_45_2
      Q2.hcardT68_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_45_2 i) (Q2.hfix68_45_2 i) _)
      colCert_68_45_3.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_45_4 (hp : 4 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 4 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 4 (transLenTr ⟨45, by decide⟩ 4 hp)) T68_45
      hfix68_45 hinj68_45 hcardT68_45
      (fun i => conj_mem_of_fixedPoints _ _ (T68_45 i) (hfix68_45 i) _)
      ⟨68, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 4 hp) Q2.T68_45_2 Q2.hfix68_45_2 Q2.hinj68_45_2
      Q2.hcardT68_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_45_2 i) (Q2.hfix68_45_2 i) _)
      colCert_68_45_4.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_45_5 (hp : 5 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 5 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 5 (transLenTr ⟨45, by decide⟩ 5 hp)) T68_45
      hfix68_45 hinj68_45 hcardT68_45
      (fun i => conj_mem_of_fixedPoints _ _ (T68_45 i) (hfix68_45 i) _)
      ⟨68, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 5 hp) Q2.T68_45_2 Q2.hfix68_45_2 Q2.hinj68_45_2
      Q2.hcardT68_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_45_2 i) (Q2.hfix68_45_2 i) _)
      colCert_68_45_5.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_45_10 (hp : 10 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 10 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 10 (transLenTr ⟨45, by decide⟩ 10 hp)) T68_45
      hfix68_45 hinj68_45 hcardT68_45
      (fun i => conj_mem_of_fixedPoints _ _ (T68_45 i) (hfix68_45 i) _)
      ⟨68, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 10 hp) Q2.T68_45_2 Q2.hfix68_45_2 Q2.hinj68_45_2
      Q2.hcardT68_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_45_2 i) (Q2.hfix68_45_2 i) _)
      colCert_68_45_10.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_45_15 (hp : 15 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 15 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 15 (transLenTr ⟨45, by decide⟩ 15 hp)) T68_45
      hfix68_45 hinj68_45 hcardT68_45
      (fun i => conj_mem_of_fixedPoints _ _ (T68_45 i) (hfix68_45 i) _)
      ⟨68, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 15 hp) Q2.T68_45_2 Q2.hfix68_45_2 Q2.hinj68_45_2
      Q2.hcardT68_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_45_2 i) (Q2.hfix68_45_2 i) _)
      colCert_68_45_15.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_45_20 (hp : 20 < (Q2.transData.getD 45 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨45, by decide⟩ : Fin 148)) (colE2 ⟨45, by decide⟩ 20 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨45, by decide⟩ : Fin 148))
        (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨45, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨45, by decide⟩ 20 (transLenTr ⟨45, by decide⟩ 20 hp)) T68_45
      hfix68_45 hinj68_45 hcardT68_45
      (fun i => conj_mem_of_fixedPoints _ _ (T68_45 i) (hfix68_45 i) _)
      ⟨68, by decide⟩ ⟨45, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨45, by decide⟩ 20 hp) Q2.T68_45_2 Q2.hfix68_45_2 Q2.hinj68_45_2
      Q2.hcardT68_45_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_45_2 i) (Q2.hfix68_45_2 i) _)
      colCert_68_45_20.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_50_0 (hp : 0 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 0 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 0 (transLenTr ⟨50, by decide⟩ 0 hp)) T68_50
      hfix68_50 hinj68_50 hcardT68_50
      (fun i => conj_mem_of_fixedPoints _ _ (T68_50 i) (hfix68_50 i) _)
      ⟨68, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 0 hp) Q2.T68_50_2 Q2.hfix68_50_2 Q2.hinj68_50_2
      Q2.hcardT68_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_50_2 i) (Q2.hfix68_50_2 i) _)
      colCert_68_50_0.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_50_1 (hp : 1 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 1 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 1 (transLenTr ⟨50, by decide⟩ 1 hp)) T68_50
      hfix68_50 hinj68_50 hcardT68_50
      (fun i => conj_mem_of_fixedPoints _ _ (T68_50 i) (hfix68_50 i) _)
      ⟨68, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 1 hp) Q2.T68_50_2 Q2.hfix68_50_2 Q2.hinj68_50_2
      Q2.hcardT68_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_50_2 i) (Q2.hfix68_50_2 i) _)
      colCert_68_50_1.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_50_2 (hp : 2 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 2 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 2 (transLenTr ⟨50, by decide⟩ 2 hp)) T68_50
      hfix68_50 hinj68_50 hcardT68_50
      (fun i => conj_mem_of_fixedPoints _ _ (T68_50 i) (hfix68_50 i) _)
      ⟨68, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 2 hp) Q2.T68_50_2 Q2.hfix68_50_2 Q2.hinj68_50_2
      Q2.hcardT68_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_50_2 i) (Q2.hfix68_50_2 i) _)
      colCert_68_50_2.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_50_3 (hp : 3 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 3 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 3 (transLenTr ⟨50, by decide⟩ 3 hp)) T68_50
      hfix68_50 hinj68_50 hcardT68_50
      (fun i => conj_mem_of_fixedPoints _ _ (T68_50 i) (hfix68_50 i) _)
      ⟨68, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 3 hp) Q2.T68_50_2 Q2.hfix68_50_2 Q2.hinj68_50_2
      Q2.hcardT68_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_50_2 i) (Q2.hfix68_50_2 i) _)
      colCert_68_50_3.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_50_4 (hp : 4 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 4 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 4 (transLenTr ⟨50, by decide⟩ 4 hp)) T68_50
      hfix68_50 hinj68_50 hcardT68_50
      (fun i => conj_mem_of_fixedPoints _ _ (T68_50 i) (hfix68_50 i) _)
      ⟨68, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 4 hp) Q2.T68_50_2 Q2.hfix68_50_2 Q2.hinj68_50_2
      Q2.hcardT68_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_50_2 i) (Q2.hfix68_50_2 i) _)
      colCert_68_50_4.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_50_5 (hp : 5 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 5 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 5 (transLenTr ⟨50, by decide⟩ 5 hp)) T68_50
      hfix68_50 hinj68_50 hcardT68_50
      (fun i => conj_mem_of_fixedPoints _ _ (T68_50 i) (hfix68_50 i) _)
      ⟨68, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 5 hp) Q2.T68_50_2 Q2.hfix68_50_2 Q2.hinj68_50_2
      Q2.hcardT68_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_50_2 i) (Q2.hfix68_50_2 i) _)
      colCert_68_50_5.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_50_10 (hp : 10 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 10 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 10 (transLenTr ⟨50, by decide⟩ 10 hp)) T68_50
      hfix68_50 hinj68_50 hcardT68_50
      (fun i => conj_mem_of_fixedPoints _ _ (T68_50 i) (hfix68_50 i) _)
      ⟨68, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 10 hp) Q2.T68_50_2 Q2.hfix68_50_2 Q2.hinj68_50_2
      Q2.hcardT68_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_50_2 i) (Q2.hfix68_50_2 i) _)
      colCert_68_50_10.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_50_15 (hp : 15 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 15 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 15 (transLenTr ⟨50, by decide⟩ 15 hp)) T68_50
      hfix68_50 hinj68_50 hcardT68_50
      (fun i => conj_mem_of_fixedPoints _ _ (T68_50 i) (hfix68_50 i) _)
      ⟨68, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 15 hp) Q2.T68_50_2 Q2.hfix68_50_2 Q2.hinj68_50_2
      Q2.hcardT68_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_50_2 i) (Q2.hfix68_50_2 i) _)
      colCert_68_50_15.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_50_20 (hp : 20 < (Q2.transData.getD 50 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨50, by decide⟩ : Fin 148)) (colE2 ⟨50, by decide⟩ 20 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨50, by decide⟩ : Fin 148))
        (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨50, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨50, by decide⟩ 20 (transLenTr ⟨50, by decide⟩ 20 hp)) T68_50
      hfix68_50 hinj68_50 hcardT68_50
      (fun i => conj_mem_of_fixedPoints _ _ (T68_50 i) (hfix68_50 i) _)
      ⟨68, by decide⟩ ⟨50, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨50, by decide⟩ 20 hp) Q2.T68_50_2 Q2.hfix68_50_2 Q2.hinj68_50_2
      Q2.hcardT68_50_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_50_2 i) (Q2.hfix68_50_2 i) _)
      colCert_68_50_20.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_0 (hp : 0 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 0 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 0 (transLenTr ⟨68, by decide⟩ 0 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 0 (transLenTr ⟨68, by decide⟩ 0 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 0 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_0.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_1 (hp : 1 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 1 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 1 (transLenTr ⟨68, by decide⟩ 1 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 1 (transLenTr ⟨68, by decide⟩ 1 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 1 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_1.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_2 (hp : 2 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 2 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 2 (transLenTr ⟨68, by decide⟩ 2 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 2 (transLenTr ⟨68, by decide⟩ 2 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 2 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_2.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_3 (hp : 3 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 3 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 3 (transLenTr ⟨68, by decide⟩ 3 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 3 (transLenTr ⟨68, by decide⟩ 3 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 3 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_3.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_4 (hp : 4 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 4 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 4 (transLenTr ⟨68, by decide⟩ 4 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 4 (transLenTr ⟨68, by decide⟩ 4 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 4 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_4.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_5 (hp : 5 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 5 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 5 (transLenTr ⟨68, by decide⟩ 5 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 5 (transLenTr ⟨68, by decide⟩ 5 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 5 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_5.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_6 (hp : 6 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 6 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 6 (transLenTr ⟨68, by decide⟩ 6 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 6 (transLenTr ⟨68, by decide⟩ 6 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 6 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_6.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_7 (hp : 7 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 7 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 7 (transLenTr ⟨68, by decide⟩ 7 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 7 (transLenTr ⟨68, by decide⟩ 7 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 7 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_7.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_8 (hp : 8 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 8 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 8 (transLenTr ⟨68, by decide⟩ 8 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 8 (transLenTr ⟨68, by decide⟩ 8 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 8 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_8.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_9 (hp : 9 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 9 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 9 (transLenTr ⟨68, by decide⟩ 9 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 9 (transLenTr ⟨68, by decide⟩ 9 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 9 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_9.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_10 (hp : 10 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 10 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 10 (transLenTr ⟨68, by decide⟩ 10 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 10 (transLenTr ⟨68, by decide⟩ 10 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 10 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_10.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_11 (hp : 11 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 11 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 11 (transLenTr ⟨68, by decide⟩ 11 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 11 (transLenTr ⟨68, by decide⟩ 11 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 11 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_11.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_12 (hp : 12 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 12 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 12 (transLenTr ⟨68, by decide⟩ 12 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 12 (transLenTr ⟨68, by decide⟩ 12 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 12 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_12.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_13 (hp : 13 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 13 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 13 (transLenTr ⟨68, by decide⟩ 13 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 13 (transLenTr ⟨68, by decide⟩ 13 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 13 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_13.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_14 (hp : 14 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 14 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 14 (transLenTr ⟨68, by decide⟩ 14 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 14 (transLenTr ⟨68, by decide⟩ 14 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 14 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_14.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_15 (hp : 15 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 15 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 15 (transLenTr ⟨68, by decide⟩ 15 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 15 (transLenTr ⟨68, by decide⟩ 15 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 15 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_15.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_16 (hp : 16 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 16 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 16 (transLenTr ⟨68, by decide⟩ 16 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 16 (transLenTr ⟨68, by decide⟩ 16 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 16 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_16.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_17 (hp : 17 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 17 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 17 (transLenTr ⟨68, by decide⟩ 17 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 17 (transLenTr ⟨68, by decide⟩ 17 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 17 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_17.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_18 (hp : 18 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 18 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 18 (transLenTr ⟨68, by decide⟩ 18 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 18 (transLenTr ⟨68, by decide⟩ 18 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 18 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_18.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_19 (hp : 19 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 19 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 19 (transLenTr ⟨68, by decide⟩ 19 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 19 (transLenTr ⟨68, by decide⟩ 19 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 19 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨68, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 19 (transLenTr ⟨68, by decide⟩ 19 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T68_68 = colFn colCertDiv_68_68_19.D1 (m := 5) from colCertDiv_68_68_19.bind1,
    show colData2 (⟨68, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 19 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T68_68_2 = colFn colCertDiv_68_68_19.D2 (m := 5) from colCertDiv_68_68_19.bind2]
  rw [alnId_68 j hj]
  exact fastcode_of_tau ⟨68, by decide⟩ _ _ _
    ((alnId_68 j hj) ▸ Q2.listedAt (⟨68, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨68, by decide⟩ : Fin 148) hj hq).1) colCertDiv_68_68_19_tau_match


theorem leaf_68_68_20 (hp : 20 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 20 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 20 (transLenTr ⟨68, by decide⟩ 20 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 20 (transLenTr ⟨68, by decide⟩ 20 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 20 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨68, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 20 (transLenTr ⟨68, by decide⟩ 20 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T68_68 = colFn colCertDiv_68_68_20.D1 (m := 5) from colCertDiv_68_68_20.bind1,
    show colData2 (⟨68, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 20 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T68_68_2 = colFn colCertDiv_68_68_20.D2 (m := 5) from colCertDiv_68_68_20.bind2]
  rw [alnId_68 j hj]
  exact fastcode_of_tau ⟨68, by decide⟩ _ _ _
    ((alnId_68 j hj) ▸ Q2.listedAt (⟨68, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨68, by decide⟩ : Fin 148) hj hq).1) colCertDiv_68_68_20_tau_match


theorem leaf_68_68_21 (hp : 21 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 21 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 21 (transLenTr ⟨68, by decide⟩ 21 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 21 (transLenTr ⟨68, by decide⟩ 21 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 21 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨68, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 21 (transLenTr ⟨68, by decide⟩ 21 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T68_68 = colFn colCertDiv_68_68_21.D1 (m := 5) from colCertDiv_68_68_21.bind1,
    show colData2 (⟨68, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 21 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T68_68_2 = colFn colCertDiv_68_68_21.D2 (m := 5) from colCertDiv_68_68_21.bind2]
  rw [alnId_68 j hj]
  exact fastcode_of_tau ⟨68, by decide⟩ _ _ _
    ((alnId_68 j hj) ▸ Q2.listedAt (⟨68, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨68, by decide⟩ : Fin 148) hj hq).1) colCertDiv_68_68_21_tau_match


theorem leaf_68_68_22 (hp : 22 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 22 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 22 (transLenTr ⟨68, by decide⟩ 22 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_fastcode_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 22 (transLenTr ⟨68, by decide⟩ 22 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 22 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      ?_).symm
  rw [show colData1 (⟨68, by decide⟩ : Fin 148)
        ((colE1 ⟨68, by decide⟩ 22 (transLenTr ⟨68, by decide⟩ 22 hp) : ↥(reps ⟨68, by decide⟩)) : Coordinate 1)
        T68_68 = colFn colCertDiv_68_68_22.D1 (m := 5) from colCertDiv_68_68_22.bind1,
    show colData2 (⟨68, by decide⟩ : Fin 148)
        ((colE2 ⟨68, by decide⟩ 22 hp : ↥(Q2.reps ⟨68, by decide⟩)) : Coordinate 2)
        Q2.T68_68_2 = colFn colCertDiv_68_68_22.D2 (m := 5) from colCertDiv_68_68_22.bind2]
  rw [alnId_68 j hj]
  exact fastcode_of_tau ⟨68, by decide⟩ _ _ _
    ((alnId_68 j hj) ▸ Q2.listedAt (⟨68, by decide⟩ : Fin 148)
      (alnCheck_rep (⟨68, by decide⟩ : Fin 148) hj hq).1) colCertDiv_68_68_22_tau_match


theorem leaf_68_68_23 (hp : 23 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 23 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 23 (transLenTr ⟨68, by decide⟩ 23 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 23 (transLenTr ⟨68, by decide⟩ 23 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 23 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_23.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_68_68_24 (hp : 24 < (Q2.transData.getD 68 []).length)
    (j : Nat) (hj : j < (repChars.getD 68 []).length)
    (hq : (normIsRep.getD 68 []).getD j false = true) :
    species (Q2.reps (⟨68, by decide⟩ : Fin 148)) (colE2 ⟨68, by decide⟩ 24 hp)
        (rowE2 (⟨68, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨68, by decide⟩ : Fin 148))
        (colE1 ⟨68, by decide⟩ 24 (transLenTr ⟨68, by decide⟩ 24 hp))
        (rowE1 (⟨68, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨68, by decide⟩ : Fin 148) ⟨68, by decide⟩ _
      (validAt ⟨68, by decide⟩ (listedAt ⟨68, by decide⟩ hj))
      (colE1 ⟨68, by decide⟩ 24 (transLenTr ⟨68, by decide⟩ 24 hp)) T68_68
      hfix68_68 hinj68_68 hcardT68_68
      (fun i => conj_mem_of_fixedPoints _ _ (T68_68 i) (hfix68_68 i) _)
      ⟨68, by decide⟩ ⟨68, by decide⟩ _
      (Q2.validAt ⟨68, by decide⟩ (Q2.listedAt ⟨68, by decide⟩
        (alnCheck_rep ⟨68, by decide⟩ hj hq).1))
      (colE2 ⟨68, by decide⟩ 24 hp) Q2.T68_68_2 Q2.hfix68_68_2 Q2.hinj68_68_2
      Q2.hcardT68_68_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T68_68_2 i) (Q2.hfix68_68_2 i) _)
      colCert_68_68_24.hD ?_).symm
  rw [alnId_68 j hj]


theorem leaf_69_8_0 (hp : 0 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 0 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 0 (transLenTr ⟨8, by decide⟩ 0 hp)) T69_8
      hfix69_8 hinj69_8 hcardT69_8
      (fun i => conj_mem_of_fixedPoints _ _ (T69_8 i) (hfix69_8 i) _)
      ⟨69, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 0 hp) Q2.T69_8_2 Q2.hfix69_8_2 Q2.hinj69_8_2
      Q2.hcardT69_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_8_2 i) (Q2.hfix69_8_2 i) _)
      colCert_69_8_0.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_8_1 (hp : 1 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 1 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 1 (transLenTr ⟨8, by decide⟩ 1 hp)) T69_8
      hfix69_8 hinj69_8 hcardT69_8
      (fun i => conj_mem_of_fixedPoints _ _ (T69_8 i) (hfix69_8 i) _)
      ⟨69, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 1 hp) Q2.T69_8_2 Q2.hfix69_8_2 Q2.hinj69_8_2
      Q2.hcardT69_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_8_2 i) (Q2.hfix69_8_2 i) _)
      colCert_69_8_1.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_8_2 (hp : 2 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 2 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 2 (transLenTr ⟨8, by decide⟩ 2 hp)) T69_8
      hfix69_8 hinj69_8 hcardT69_8
      (fun i => conj_mem_of_fixedPoints _ _ (T69_8 i) (hfix69_8 i) _)
      ⟨69, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 2 hp) Q2.T69_8_2 Q2.hfix69_8_2 Q2.hinj69_8_2
      Q2.hcardT69_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_8_2 i) (Q2.hfix69_8_2 i) _)
      colCert_69_8_2.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_8_3 (hp : 3 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 3 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 3 (transLenTr ⟨8, by decide⟩ 3 hp)) T69_8
      hfix69_8 hinj69_8 hcardT69_8
      (fun i => conj_mem_of_fixedPoints _ _ (T69_8 i) (hfix69_8 i) _)
      ⟨69, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 3 hp) Q2.T69_8_2 Q2.hfix69_8_2 Q2.hinj69_8_2
      Q2.hcardT69_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_8_2 i) (Q2.hfix69_8_2 i) _)
      colCert_69_8_3.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_8_4 (hp : 4 < (Q2.transData.getD 8 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨8, by decide⟩ : Fin 148)) (colE2 ⟨8, by decide⟩ 4 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨8, by decide⟩ : Fin 148))
        (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨8, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨8, by decide⟩ 4 (transLenTr ⟨8, by decide⟩ 4 hp)) T69_8
      hfix69_8 hinj69_8 hcardT69_8
      (fun i => conj_mem_of_fixedPoints _ _ (T69_8 i) (hfix69_8 i) _)
      ⟨69, by decide⟩ ⟨8, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨8, by decide⟩ 4 hp) Q2.T69_8_2 Q2.hfix69_8_2 Q2.hinj69_8_2
      Q2.hcardT69_8_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_8_2 i) (Q2.hfix69_8_2 i) _)
      colCert_69_8_4.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_12_0 (hp : 0 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 0 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 0 (transLenTr ⟨12, by decide⟩ 0 hp)) T69_12
      hfix69_12 hinj69_12 hcardT69_12
      (fun i => conj_mem_of_fixedPoints _ _ (T69_12 i) (hfix69_12 i) _)
      ⟨69, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 0 hp) Q2.T69_12_2 Q2.hfix69_12_2 Q2.hinj69_12_2
      Q2.hcardT69_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_12_2 i) (Q2.hfix69_12_2 i) _)
      colCert_69_12_0.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_12_1 (hp : 1 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 1 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 1 (transLenTr ⟨12, by decide⟩ 1 hp)) T69_12
      hfix69_12 hinj69_12 hcardT69_12
      (fun i => conj_mem_of_fixedPoints _ _ (T69_12 i) (hfix69_12 i) _)
      ⟨69, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 1 hp) Q2.T69_12_2 Q2.hfix69_12_2 Q2.hinj69_12_2
      Q2.hcardT69_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_12_2 i) (Q2.hfix69_12_2 i) _)
      colCert_69_12_1.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_12_2 (hp : 2 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 2 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 2 (transLenTr ⟨12, by decide⟩ 2 hp)) T69_12
      hfix69_12 hinj69_12 hcardT69_12
      (fun i => conj_mem_of_fixedPoints _ _ (T69_12 i) (hfix69_12 i) _)
      ⟨69, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 2 hp) Q2.T69_12_2 Q2.hfix69_12_2 Q2.hinj69_12_2
      Q2.hcardT69_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_12_2 i) (Q2.hfix69_12_2 i) _)
      colCert_69_12_2.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_12_3 (hp : 3 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 3 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 3 (transLenTr ⟨12, by decide⟩ 3 hp)) T69_12
      hfix69_12 hinj69_12 hcardT69_12
      (fun i => conj_mem_of_fixedPoints _ _ (T69_12 i) (hfix69_12 i) _)
      ⟨69, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 3 hp) Q2.T69_12_2 Q2.hfix69_12_2 Q2.hinj69_12_2
      Q2.hcardT69_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_12_2 i) (Q2.hfix69_12_2 i) _)
      colCert_69_12_3.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_12_4 (hp : 4 < (Q2.transData.getD 12 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨12, by decide⟩ : Fin 148)) (colE2 ⟨12, by decide⟩ 4 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨12, by decide⟩ : Fin 148))
        (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨12, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨12, by decide⟩ 4 (transLenTr ⟨12, by decide⟩ 4 hp)) T69_12
      hfix69_12 hinj69_12 hcardT69_12
      (fun i => conj_mem_of_fixedPoints _ _ (T69_12 i) (hfix69_12 i) _)
      ⟨69, by decide⟩ ⟨12, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨12, by decide⟩ 4 hp) Q2.T69_12_2 Q2.hfix69_12_2 Q2.hinj69_12_2
      Q2.hcardT69_12_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_12_2 i) (Q2.hfix69_12_2 i) _)
      colCert_69_12_4.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_26_0 (hp : 0 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 0 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 0 (transLenTr ⟨26, by decide⟩ 0 hp)) T69_26
      hfix69_26 hinj69_26 hcardT69_26
      (fun i => conj_mem_of_fixedPoints _ _ (T69_26 i) (hfix69_26 i) _)
      ⟨69, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 0 hp) Q2.T69_26_2 Q2.hfix69_26_2 Q2.hinj69_26_2
      Q2.hcardT69_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_26_2 i) (Q2.hfix69_26_2 i) _)
      colCert_69_26_0.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_26_1 (hp : 1 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 1 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 1 (transLenTr ⟨26, by decide⟩ 1 hp)) T69_26
      hfix69_26 hinj69_26 hcardT69_26
      (fun i => conj_mem_of_fixedPoints _ _ (T69_26 i) (hfix69_26 i) _)
      ⟨69, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 1 hp) Q2.T69_26_2 Q2.hfix69_26_2 Q2.hinj69_26_2
      Q2.hcardT69_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_26_2 i) (Q2.hfix69_26_2 i) _)
      colCert_69_26_1.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_26_2 (hp : 2 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 2 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 2 (transLenTr ⟨26, by decide⟩ 2 hp)) T69_26
      hfix69_26 hinj69_26 hcardT69_26
      (fun i => conj_mem_of_fixedPoints _ _ (T69_26 i) (hfix69_26 i) _)
      ⟨69, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 2 hp) Q2.T69_26_2 Q2.hfix69_26_2 Q2.hinj69_26_2
      Q2.hcardT69_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_26_2 i) (Q2.hfix69_26_2 i) _)
      colCert_69_26_2.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_26_3 (hp : 3 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 3 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 3 (transLenTr ⟨26, by decide⟩ 3 hp)) T69_26
      hfix69_26 hinj69_26 hcardT69_26
      (fun i => conj_mem_of_fixedPoints _ _ (T69_26 i) (hfix69_26 i) _)
      ⟨69, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 3 hp) Q2.T69_26_2 Q2.hfix69_26_2 Q2.hinj69_26_2
      Q2.hcardT69_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_26_2 i) (Q2.hfix69_26_2 i) _)
      colCert_69_26_3.hD ?_).symm
  rw [alnId_69 j hj]


theorem leaf_69_26_4 (hp : 4 < (Q2.transData.getD 26 []).length)
    (j : Nat) (hj : j < (repChars.getD 69 []).length)
    (hq : (normIsRep.getD 69 []).getD j false = true) :
    species (Q2.reps (⟨26, by decide⟩ : Fin 148)) (colE2 ⟨26, by decide⟩ 4 hp)
        (rowE2 (⟨69, by decide⟩ : Fin 148) j hj hq)
      = species (reps (⟨26, by decide⟩ : Fin 148))
        (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp))
        (rowE1 (⟨69, by decide⟩ : Fin 148) j hj) := by
  rw [rowE1, rowE2]
  refine (species_eq_of_data_eq (⟨69, by decide⟩ : Fin 148) ⟨26, by decide⟩ _
      (validAt ⟨69, by decide⟩ (listedAt ⟨69, by decide⟩ hj))
      (colE1 ⟨26, by decide⟩ 4 (transLenTr ⟨26, by decide⟩ 4 hp)) T69_26
      hfix69_26 hinj69_26 hcardT69_26
      (fun i => conj_mem_of_fixedPoints _ _ (T69_26 i) (hfix69_26 i) _)
      ⟨69, by decide⟩ ⟨26, by decide⟩ _
      (Q2.validAt ⟨69, by decide⟩ (Q2.listedAt ⟨69, by decide⟩
        (alnCheck_rep ⟨69, by decide⟩ hj hq).1))
      (colE2 ⟨26, by decide⟩ 4 hp) Q2.T69_26_2 Q2.hfix69_26_2 Q2.hinj69_26_2
      Q2.hcardT69_26_2
      (fun i => conj_mem_of_fixedPoints _ _ (Q2.T69_26_2 i) (Q2.hfix69_26_2 i) _)
      colCert_69_26_4.hD ?_).symm
  rw [alnId_69 j hj]


end LeanDring.P5Presentation
